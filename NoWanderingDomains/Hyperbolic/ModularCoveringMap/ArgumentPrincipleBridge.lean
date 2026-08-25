/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularCoveringMap.ArcNonvanishing
import NoWanderingDomains.Hyperbolic.WindingNumber.TruncatedArgumentPrinciple
import NoWanderingDomains.Hyperbolic.PathWinding.LogLiftHomotopy

/-! # The argument principle on F_Y and the contour bridge

The argument principle on the `F_Y` region: the `(2πi)⁻¹`-normalized six-term boundary
integral of `λ′/(λ − w)` is a natural number, equal to the divisor sum of `λ − w` on
the truncated region. The deep-cusp reference value `w₀` whose unique `F°`-preimage is
a single simple point, the bridge identifying the six-term boundary expression with the
contour integral of `(z − w)⁻¹` along the image curve `λ ∘ ∂F_Y`, and homotopy
invariance of that contour integral via a jointly continuous log lift.
-/

namespace NoWanderingDomains
open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-! ## The argument principle on the F_Y region -/

/-- **AP application packager.** Direct wrapper
around `cIntegralLogDeriv_isNat_of_nonzero_on_rectMinusUpperHalfDisk`
applied to `g(τ) = λ(τ) − w` over the F_Y region. Returns the existence
of a natural number `n` such that `(2πi)⁻¹ · (boundary integral) = n`.

The hypotheses include all six boundary non-vanishing conditions
(the four rectangle edges + bot_left/bot_right strips + arc), which
the caller supplies via the existing `_F_Y_left_edge_ne`,
`_F_Y_right_edge_ne`, `_F_Y_top_edge_ne` (+ a `Y ≥ Y₀` cascade),
`_F_Y_bot_left_strip_ne`, `_F_Y_bot_right_strip_ne`, and `_F_Y_arc_ne`
helpers in the path-(a) chain. -/
theorem modularLambdaH_F_Y_AP_integral_eq_nat_form
    {w : ℂ} {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (_hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0) :
    ∃ n : ℕ, (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      (∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = (n : ℂ) := by
  -- Apply cIntegralLogDeriv_isNat_of_nonzero_on_rectMinusUpperHalfDisk to
  -- g = fun τ => modularLambdaH τ - w, e = 1/2 + δi, a = 0, b = 1, d = Y.
  set g : ℂ → ℂ := fun τ => modularLambdaH τ - w with hg_def
  set e : ℂ := (1 / 2 : ℂ) + (δ : ℂ) * Complex.I with he_def
  have he_re : e.re = 1 / 2 := by
    rw [he_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
    rw [h_half_re]; ring
  have he_im : e.im = δ := by
    rw [he_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [h_half_im]; ring
  -- AP theorem prerequisites.
  have hab : (0 : ℝ) < 1 := by norm_num
  have h_a_lt : (0 : ℝ) < e.re - R₀ := by rw [he_re]; linarith
  have h_lt_b : e.re + R₀ < 1 := by rw [he_re]; linarith
  have h_e_im_R0_lt_d : e.im + R₀ < Y := by rw [he_im]; exact h_δR_lt_Y
  -- Analyticity of g on F_Y.
  have hg_an : AnalyticOnNhd ℂ g
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc e.im Y) \ Metric.ball e R₀) := by
    rw [he_im, he_def]
    exact modularLambdaH_F_Y_analytic w hδ _hδY hR₀_pos
  -- Boundary non-vanishing for g (= λ − w).
  have hg_bot_left' : ∀ x ∈ Set.Icc (0 : ℝ) (e.re - R₀),
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0 := by
    rw [he_re, he_im]; intro x hx; exact hg_bot_left x hx
  have hg_bot_right' : ∀ x ∈ Set.Icc (e.re + R₀) 1,
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0 := by
    rw [he_re, he_im]; intro x hx; exact hg_bot_right x hx
  have hg_top' : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      g ((x : ℂ) + (Y : ℂ) * Complex.I) ≠ 0 := by
    intro x hx; exact hg_top x hx
  have hg_right' : ∀ y ∈ Set.Icc e.im Y,
      g ((1 : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    rw [he_im]; intro y hy; exact hg_right y hy
  have hg_left' : ∀ y ∈ Set.Icc e.im Y,
      g ((0 : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    rw [he_im]; intro y hy; exact hg_left y hy
  have hg_arc' : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      g (_root_.circleMap e R₀ θ) ≠ 0 := by
    rw [he_def]; intro θ hθ; exact hg_arc θ hθ
  -- Apply the AP theorem.
  obtain ⟨n, hn⟩ := cIntegralLogDeriv_isNat_of_nonzero_on_rectMinusUpperHalfDisk
    g 0 1 Y e R₀ hab hR₀_pos h_a_lt h_lt_b h_e_im_R0_lt_d
    hg_an hg_bot_left' hg_bot_right' hg_top' hg_right' hg_left' hg_arc'
  refine ⟨n, ?_⟩
  -- Convert deriv g to deriv modularLambdaH.
  have h_deriv : ∀ τ : ℂ, deriv g τ = deriv modularLambdaH τ := fun τ => by
    rw [hg_def]; exact deriv_sub_const w
  -- Rewrite hn to match the goal: substitute e.re = 1/2, e.im = δ,
  -- unfold e, unfold g, replace deriv g with deriv modularLambdaH.
  rw [he_re, he_im] at hn
  simp_rw [h_deriv, hg_def, he_def] at hn
  convert! hn using 2

/-- **F_Y argument principle, divisor-sum form.** The `(2πi)⁻¹`-normalized
six-term boundary integral of `λ'/(λ − w)` over `∂F_Y` equals the total
divisor sum (the zero count with multiplicity) of `λ − w` on the
truncated region. Wrapper around
`Complex.cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk`
specialized to `g := λ − w`, with `deriv g` converted to `deriv λ`. -/
theorem modularLambdaH_F_Y_AP_integral_eq_divisor_sum
    {w : ℂ} {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0) :
    (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      (∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) =
    ((∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat : ℂ) := by
  set g : ℂ → ℂ := fun τ => modularLambdaH τ - w with hg_def
  set e : ℂ := (1 / 2 : ℂ) + (δ : ℂ) * Complex.I with he_def
  have he_re : e.re = 1 / 2 := by
    rw [he_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
    rw [h_half_re]; ring
  have he_im : e.im = δ := by
    rw [he_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [h_half_im]; ring
  have hab : (0 : ℝ) < 1 := by norm_num
  have h_a_lt : (0 : ℝ) < e.re - R₀ := by rw [he_re]; linarith
  have h_lt_b : e.re + R₀ < 1 := by rw [he_re]; linarith
  have h_e_im_R0_lt_d : e.im + R₀ < Y := by rw [he_im]; exact h_δR_lt_Y
  have hg_an : AnalyticOnNhd ℂ g
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc e.im Y) \ Metric.ball e R₀) := by
    rw [he_im, he_def]
    exact modularLambdaH_F_Y_analytic w hδ hδY hR₀_pos
  have hg_bot_left' : ∀ x ∈ Set.Icc (0 : ℝ) (e.re - R₀),
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0 := by
    rw [he_re, he_im]; intro x hx; exact hg_bot_left x hx
  have hg_bot_right' : ∀ x ∈ Set.Icc (e.re + R₀) 1,
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0 := by
    rw [he_re, he_im]; intro x hx; exact hg_bot_right x hx
  have hg_top' : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      g ((x : ℂ) + (Y : ℂ) * Complex.I) ≠ 0 := by
    intro x hx; exact hg_top x hx
  have hg_right' : ∀ y ∈ Set.Icc e.im Y,
      g ((1 : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    rw [he_im]; intro y hy; exact hg_right y hy
  have hg_left' : ∀ y ∈ Set.Icc e.im Y,
      g ((0 : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    rw [he_im]; intro y hy; exact hg_left y hy
  have hg_arc' : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      g (_root_.circleMap e R₀ θ) ≠ 0 := by
    rw [he_def]; intro θ hθ; exact hg_arc θ hθ
  have hn := Complex.cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk
    g 0 1 Y e R₀ hab hR₀_pos h_a_lt h_lt_b h_e_im_R0_lt_d
    hg_an hg_bot_left' hg_bot_right' hg_top' hg_right' hg_left' hg_arc'
  have h_deriv : ∀ τ : ℂ, deriv g τ = deriv modularLambdaH τ := fun τ => by
    rw [hg_def]; exact deriv_sub_const w
  rw [he_re, he_im] at hn
  simp_rw [h_deriv, hg_def, he_def] at hn
  convert! hn using 2


/-! ## The deep-cusp reference value -/

set_option maxHeartbeats 400000 in
-- The quantitative cusp-chart estimates make this declaration elaboration-heavy.
/-- **Deep-cusp reference value.** There is a value `w₀ ∈ ℍ` whose full
set of `λ`-preimages in the open fundamental domain `F°` is the single
point `τ₀ = 1/2 + T·i`, at which `λ' ≠ 0`. Deep in the cusp the
`q = exp(iπτ)`-chart is injective (`λ̃'(0) = 16 ≠ 0`, mean-value
estimate), the strip makes `q` itself injective, and away from the
cusp `‖λ‖` is bounded below by a compact-band minimum, which `‖w₀‖`
undercuts for `T` large. -/
theorem modularLambdaH_cusp_reference_value :
    ∃ (w₀ : ℂ) (τ₀ : ℂ), 0 < w₀.im ∧
      τ₀ ∈ Gamma2FundamentalDomainInterior ∧
      modularLambdaH τ₀ = w₀ ∧
      deriv modularLambdaH τ₀ ≠ 0 ∧
      ∀ τ ∈ Gamma2FundamentalDomainInterior, modularLambdaH τ = w₀ → τ = τ₀ := by
  -- ====================================================================
  -- Step 0a: pure arithmetic helpers, proved first (in an empty
  -- context) so that the nonlinear-arithmetic searches stay cheap.
  -- ====================================================================
  -- square-root comparison
  have h_sq_lt : ∀ a b : ℝ, 0 ≤ a → 0 < b → a ^ 2 < b ^ 2 → a < b := by
    intro a b ha hb h
    nlinarith
  -- squaring `1 < a`
  have h_one_lt_sq : ∀ a : ℝ, 1 < a → 1 < a ^ 2 := by
    intro a h
    nlinarith
  -- the semicircle constraint in coordinates
  have h_semi_helper : ∀ x y : ℝ, 1 < (2 * x - 1) ^ 2 + (2 * y) ^ 2 →
      x * (1 - x) < y ^ 2 := by
    intro x y h
    nlinarith
  -- cusp-0 band geometry: small `Im` and `Re ≤ 1/2` force `|σ| < 2·Im σ`
  have h_band0 : ∀ x y : ℝ, 0 < x → x ≤ 1/2 → 0 < y → y < 1/4 →
      x * (1 - x) < y ^ 2 → x * x + y * y < (2 * y) ^ 2 := by
    intro x y hx hx2 hy hy4 hs
    have h1 : x < 2 * y ^ 2 := by
      nlinarith [mul_nonneg hx.le (show (0:ℝ) ≤ 1/2 - x by linarith)]
    have h2 : 2 * y ^ 2 < y / 2 := by
      nlinarith [mul_pos hy (show (0:ℝ) < 1/4 - y by linarith)]
    nlinarith [mul_pos (show (0:ℝ) < y/2 - x by linarith)
      (show (0:ℝ) < y/2 + x by linarith), mul_pos hy hy]
  -- cusp-1 band geometry: small `Im` and `Re > 1/2` force `|σ−1| < 2·Im σ`
  have h_band1 : ∀ x y : ℝ, x < 1 → 1/2 < x → 0 < y → y < 1/4 →
      x * (1 - x) < y ^ 2 → (x - 1) * (x - 1) + y * y < (2 * y) ^ 2 := by
    intro x y hx1 hx2 hy hy4 hs
    have h1 : 1 - x < 2 * y ^ 2 := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ x - 1/2 by linarith)
        (show (0:ℝ) ≤ 1 - x by linarith)]
    have h2 : 2 * y ^ 2 < y / 2 := by
      nlinarith [mul_pos hy (show (0:ℝ) < 1/4 - y by linarith)]
    nlinarith [mul_pos (show (0:ℝ) < y/2 - (1 - x) by linarith)
      (show (0:ℝ) < y/2 + (1 - x) by linarith), mul_pos hy hy]
  -- positivity of the deep-cusp derivative lower bound
  have h_deep_pos : ∀ p v : ℝ, 3 < p → p < 4 → 0 < v → v < 1/10000 →
      0 < 16 * p * v - 256 * p * v ^ 2 - 2112 * p * v ^ 3 - 100000 * v ^ 4 := by
    intro p v hp3 hp4 hv hv4
    have hv1 : v ≤ 1 := by linarith
    have h2 : v ^ 2 ≤ (1/10000) * v := by nlinarith
    have h3 : v ^ 3 ≤ v ^ 2 := by nlinarith [sq_nonneg v]
    have h21 : v ^ 2 ≤ 1 := by nlinarith
    have h4 : v ^ 4 ≤ v ^ 2 := by nlinarith [sq_nonneg v, sq_nonneg (v ^ 2)]
    have t1 : 256 * p * v ^ 2 ≤ 1024 * v ^ 2 := by nlinarith [sq_nonneg v]
    have t2 : 2112 * p * v ^ 3 ≤ 8448 * v ^ 3 := by nlinarith [pow_nonneg hv.le 3]
    have t3 : 48 * v ≤ 16 * p * v := by nlinarith
    have h3nn : (0:ℝ) ≤ v ^ 3 := pow_nonneg hv.le 3
    linarith
  -- smallness of the cusp-derivative error terms on `‖q‖ ≤ 1/100`
  have h_small_bound : ∀ t : ℝ, 0 ≤ t → t ≤ 1/100 →
      31000 * t ^ 3 + (2112 * t ^ 2 + 256 * t) ≤ 8 := by
    intro t h0 h1
    have hsq : t ^ 2 ≤ (1/100) * t := by nlinarith
    have hcb : t ^ 3 ≤ (1/100) * t ^ 2 := by nlinarith [sq_nonneg t]
    linarith
  -- ====================================================================
  -- Step 0b: numerical constants.
  -- ====================================================================
  have hπ_pos : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ_gt3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hπ_lt4 : Real.pi < 4 := Real.pi_lt_four
  have h_exp_pi_gt : (22:ℝ) < Real.exp Real.pi := exp_pi_gt_22
  have h_exp_pi_pos : (0:ℝ) < Real.exp Real.pi := Real.exp_pos _
  -- `exp π < 100`
  have h_exp_pi_lt : Real.exp Real.pi < 100 := by
    have h1 : Real.exp Real.pi < Real.exp 4 := Real.exp_lt_exp.mpr hπ_lt4
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
    have he := Real.exp_one_lt_d9
    have he_pos := Real.exp_pos 1
    have he2 : Real.exp 1 * Real.exp 1 < 7.389057 := by nlinarith [he, he_pos]
    have he4 : (Real.exp 1 * Real.exp 1) * (Real.exp 1 * Real.exp 1) < 60 := by
      nlinarith [he2, mul_pos he_pos he_pos]
    nlinarith [he4, h1, h4]
  -- `1/100 ≤ exp(−π)`
  have h_inv100_le : (1/100 : ℝ) ≤ Real.exp (-Real.pi) := by
    have h2 : Real.exp (-Real.pi) * Real.exp Real.pi = 1 := by
      rw [← Real.exp_add]; simp
    have h_mul := mul_lt_mul_of_pos_left h_exp_pi_lt (Real.exp_pos (-Real.pi))
    rw [h2] at h_mul
    linarith only [h_mul]
  -- `484 < (exp π)²` and `10000 < (exp π)³`
  have h484 : (484:ℝ) < Real.exp Real.pi ^ 2 := by
    nlinarith [sq_nonneg (Real.exp Real.pi - 22), h_exp_pi_gt]
  have h10000 : (10000:ℝ) < Real.exp Real.pi ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h484.le) (sub_nonneg.mpr h_exp_pi_gt.le),
      h484, h_exp_pi_gt]
  -- `exp(−2π) < 1/100`
  have h_exp_2pi_lt : Real.exp (-(Real.pi * 2)) < 1/100 := by
    have h2 : Real.exp (-(Real.pi * 2)) * Real.exp Real.pi ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add,
        show -(Real.pi * 2) + (2:ℕ) * Real.pi = 0 by push_cast; ring]
      exact Real.exp_zero
    have h_mul := mul_lt_mul_of_pos_left h484 (Real.exp_pos (-(Real.pi * 2)))
    rw [h2] at h_mul
    linarith only [h_mul, Real.exp_pos (-(Real.pi * 2))]
  -- ====================================================================
  -- Step 1: the cusp chart `λ̃` is quantitatively injective on
  -- `closedBall 0 (1/100)`, via `‖λ̃' − 16‖ ≤ 8` there and the MVT.
  -- ====================================================================
  have h_diff_cusp : ∀ z : ℂ, ‖z‖ ≤ 1/100 → DifferentiableAt ℂ modularLambdaH_cusp z := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz_ne
    · exact modularLambdaH_cusp_differentiableAt_zero
    · exact modularLambdaH_cusp_differentiableAt_of_norm_lt_one hz_ne
        (lt_of_le_of_lt hz (by norm_num))
  have h_deriv_cusp_bound : ∀ z : ℂ, ‖z‖ ≤ 1/100 →
      ‖deriv modularLambdaH_cusp z - 16‖ ≤ 8 := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz_ne
    · rw [modularLambdaH_cusp_deriv_zero]
      simp
    · have hz_le : ‖z‖ ≤ Real.exp (-Real.pi) := le_trans hz h_inv100_le
      have h_w := modularLambdaH_cusp_deriv_sub_two_term_le_widened hz_le hz_ne
      have h_split : deriv modularLambdaH_cusp z - 16 =
          (deriv modularLambdaH_cusp z - 16 + 256 * z - 2112 * z ^ 2) +
            (2112 * z ^ 2 - 256 * z) := by ring
      rw [h_split]
      refine le_trans (norm_add_le _ _) ?_
      have h_t2 : ‖(2112:ℂ) * z ^ 2 - 256 * z‖ ≤ 2112 * ‖z‖ ^ 2 + 256 * ‖z‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul, norm_mul, norm_pow]
        have h1 : ‖(2112:ℂ)‖ = 2112 := by simp
        have h2 : ‖(256:ℂ)‖ = 256 := by simp
        rw [h1, h2]
      linarith only [h_w, h_t2, h_small_bound ‖z‖ (norm_nonneg z) hz]
  have h_cusp_injOn : ∀ x ∈ Metric.closedBall (0:ℂ) (1/100),
      ∀ y ∈ Metric.closedBall (0:ℂ) (1/100),
      modularLambdaH_cusp x = modularLambdaH_cusp y → x = y := by
    intro x hx y hy h_val_eq
    have h_ball_norm : ∀ z : ℂ, z ∈ Metric.closedBall (0:ℂ) (1/100) → ‖z‖ ≤ 1/100 := by
      intro z hz
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    have h_hasDeriv : ∀ z : ℂ, ‖z‖ ≤ 1/100 →
        HasDerivAt (fun w : ℂ => modularLambdaH_cusp w - 16 * w)
          (deriv modularLambdaH_cusp z - 16) z := by
      intro z hz
      have h1 : HasDerivAt modularLambdaH_cusp (deriv modularLambdaH_cusp z) z :=
        (h_diff_cusp z hz).hasDerivAt
      have h2 : HasDerivAt (fun w : ℂ => (16:ℂ) * w) 16 z := by
        simpa using (hasDerivAt_id z).const_mul (16:ℂ)
      exact h1.sub h2
    have h_diff_f : ∀ z ∈ Metric.closedBall (0:ℂ) (1/100),
        DifferentiableAt ℂ (fun w : ℂ => modularLambdaH_cusp w - 16 * w) z := by
      intro z hz
      exact (h_hasDeriv z (h_ball_norm z hz)).differentiableAt
    have h_deriv_f_le : ∀ z ∈ Metric.closedBall (0:ℂ) (1/100),
        ‖deriv (fun w : ℂ => modularLambdaH_cusp w - 16 * w) z‖ ≤ 8 := by
      intro z hz
      rw [(h_hasDeriv z (h_ball_norm z hz)).deriv]
      exact h_deriv_cusp_bound z (h_ball_norm z hz)
    have h_mvt : ‖(modularLambdaH_cusp x - 16 * x) - (modularLambdaH_cusp y - 16 * y)‖ ≤
        8 * ‖x - y‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le h_diff_f h_deriv_f_le
        (convex_closedBall _ _) hy hx
    have h_diff_eq : (modularLambdaH_cusp x - 16 * x) - (modularLambdaH_cusp y - 16 * y) =
        -(16 * (x - y)) := by
      rw [h_val_eq]; ring
    rw [h_diff_eq, norm_neg, norm_mul] at h_mvt
    have h16 : ‖(16:ℂ)‖ = 16 := by simp
    rw [h16] at h_mvt
    have h_zero : ‖x - y‖ = 0 := by
      linarith only [h_mvt, norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h_zero)
  -- ====================================================================
  -- Step 2: cusp-0 and cusp-1 control, extracted from the tendsto lemmas.
  -- ====================================================================
  obtain ⟨δ₀, hδ₀_pos, h_cusp0⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp modularLambdaH_cusp_zero_tendsto_one_in_F
      (1/2) (by norm_num)
  have h_cusp1_ev : ∀ᶠ σ in nhdsWithin (1:ℂ) Gamma2FundamentalDomainInterior,
      (1:ℝ) ≤ ‖modularLambdaH σ‖ :=
    modularLambdaH_cusp_one_tendsto_norm_atTop_in_F.eventually (Filter.eventually_ge_atTop 1)
  obtain ⟨δ₁, hδ₁_pos, h_cusp1⟩ := Metric.mem_nhdsWithin_iff.mp h_cusp1_ev
  -- the cusp-cutoff height ε₀
  set ε₀ : ℝ := min (min δ₀ δ₁ / 2) (1/4) with hε₀_def
  have hε₀_pos : 0 < ε₀ := lt_min (half_pos (lt_min hδ₀_pos hδ₁_pos)) (by norm_num)
  have hε₀_le_quarter : ε₀ ≤ 1/4 := min_le_right _ _
  have h_2ε₀_le_δ₀ : 2 * ε₀ ≤ δ₀ := by
    have h1 : ε₀ ≤ min δ₀ δ₁ / 2 := min_le_left _ _
    have h2 : min δ₀ δ₁ ≤ δ₀ := min_le_left _ _
    linarith only [h1, h2]
  have h_2ε₀_le_δ₁ : 2 * ε₀ ≤ δ₁ := by
    have h1 : ε₀ ≤ min δ₀ δ₁ / 2 := min_le_left _ _
    have h2 : min δ₀ δ₁ ≤ δ₁ := min_le_right _ _
    linarith only [h1, h2]
  -- ====================================================================
  -- Step 3: compactness minimum on the middle band, and the lower bound
  -- `c` for `‖λ‖` on all of `F^o ∩ {Im ≤ 2}`.
  -- ====================================================================
  set K : Set ℂ := Metric.closedBall (0:ℂ) 3 ∩ {z : ℂ | ε₀ ≤ z.im} with hK_def
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (0:ℂ) 3).inter_right
      (isClosed_le continuous_const Complex.continuous_im)
  have hK_pos_im : ∀ z ∈ K, 0 < z.im := fun z hz => lt_of_lt_of_le hε₀_pos hz.2
  have hK_ne : K.Nonempty := by
    refine ⟨(ε₀ : ℂ) * Complex.I, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
        Complex.norm_I, Real.norm_eq_abs, abs_of_pos hε₀_pos, mul_one]
      linarith only [hε₀_le_quarter]
    · change ε₀ ≤ ((ε₀ : ℂ) * Complex.I).im
      simp
  have h_cont : ContinuousOn (fun z => ‖modularLambdaH z‖) K := by
    intro z hz
    exact ((modularLambdaH_differentiableAt_of_im_pos
      (hK_pos_im z hz)).continuousAt.continuousWithinAt).norm
  obtain ⟨zmin, hzmin_mem, hzmin_min⟩ := hK_compact.exists_isMinOn hK_ne h_cont
  set c : ℝ := min (‖modularLambdaH zmin‖) (1/2) with hc_def
  have hc_pos : 0 < c :=
    lt_min (norm_pos_iff.mpr (modularLambdaH_ne_zero (hK_pos_im zmin hzmin_mem)))
      (by norm_num)
  have hc_le_half : c ≤ 1/2 := min_le_right _ _
  -- The lower bound on the sub-height-2 part of `F^o`.
  have h_lower : ∀ σ ∈ Gamma2FundamentalDomainInterior,
      σ.im ≤ 2 → c ≤ ‖modularLambdaH σ‖ := by
    intro σ hσ hσ_im_le
    obtain ⟨hσ_im_pos, hσ_re_pos, hσ_re_lt, hσ_semi⟩ := hσ
    by_cases h_im_case : ε₀ ≤ σ.im
    · -- middle band: compactness minimum
      have hσ_norm_le : ‖σ‖ ≤ 3 := by
        have h := Complex.norm_le_abs_re_add_abs_im σ
        rw [abs_of_pos hσ_re_pos, abs_of_pos hσ_im_pos] at h
        linarith only [h, hσ_re_lt, hσ_im_le]
      have hσK : σ ∈ K := by
        constructor
        · rw [Metric.mem_closedBall, dist_zero_right]; exact hσ_norm_le
        · exact h_im_case
      calc c ≤ ‖modularLambdaH zmin‖ := min_le_left _ _
        _ ≤ ‖modularLambdaH σ‖ := hzmin_min hσK
    · rw [not_le] at h_im_case
      -- the semicircle constraint forces `Re·(1−Re) < Im²`
      have h_sq_gt : 1 < ‖2 * σ - 1‖ ^ 2 := h_one_lt_sq _ hσ_semi
      have h_norm_sq_eq : ‖2 * σ - 1‖ ^ 2 = (2 * σ.re - 1) ^ 2 + (2 * σ.im) ^ 2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
          Complex.mul_im]
        ring
      rw [h_norm_sq_eq] at h_sq_gt
      have h_semi_sq : σ.re * (1 - σ.re) < σ.im ^ 2 := h_semi_helper σ.re σ.im h_sq_gt
      have hσ_im_lt_quarter : σ.im < 1/4 :=
        lt_of_lt_of_le h_im_case hε₀_le_quarter
      by_cases h_re_half : σ.re ≤ 1/2
      · -- near the cusp 0
        have h_norm_sq : ‖σ‖ ^ 2 < (2 * σ.im) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          exact h_band0 σ.re σ.im hσ_re_pos h_re_half hσ_im_pos hσ_im_lt_quarter h_semi_sq
        have h_norm_lt : ‖σ‖ < 2 * σ.im :=
          h_sq_lt ‖σ‖ (2 * σ.im) (norm_nonneg σ)
            (by linarith only [hσ_im_pos]) h_norm_sq
        have h_dist : dist σ 0 < δ₀ := by
          rw [dist_zero_right]
          calc ‖σ‖ < 2 * σ.im := h_norm_lt
            _ < 2 * ε₀ := by linarith only [h_im_case]
            _ ≤ δ₀ := h_2ε₀_le_δ₀
        have h_close := h_cusp0 ⟨hσ_im_pos, hσ_re_pos, hσ_re_lt, hσ_semi⟩ h_dist
        rw [dist_eq_norm] at h_close
        have h_tri : (1:ℝ) ≤ ‖modularLambdaH σ‖ + ‖modularLambdaH σ - 1‖ := by
          have h := norm_sub_le (modularLambdaH σ) (modularLambdaH σ - 1)
          have h2 : modularLambdaH σ - (modularLambdaH σ - 1) = 1 := by ring
          rw [h2, norm_one] at h
          exact h
        linarith only [h_tri, h_close, hc_le_half]
      · -- near the cusp 1
        rw [not_le] at h_re_half
        have h_norm_sq : ‖σ - 1‖ ^ 2 < (2 * σ.im) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
            sub_zero]
          exact h_band1 σ.re σ.im hσ_re_lt h_re_half hσ_im_pos hσ_im_lt_quarter h_semi_sq
        have h_norm_lt : ‖σ - 1‖ < 2 * σ.im :=
          h_sq_lt ‖σ - 1‖ (2 * σ.im) (norm_nonneg (σ - 1))
            (by linarith only [hσ_im_pos]) h_norm_sq
        have h_mem_ball : σ ∈ Metric.ball (1:ℂ) δ₁ := by
          rw [Metric.mem_ball, dist_eq_norm]
          calc ‖σ - 1‖ < 2 * σ.im := h_norm_lt
            _ < 2 * ε₀ := by linarith only [h_im_case]
            _ ≤ δ₁ := h_2ε₀_le_δ₁
        have h_ge_one : (1:ℝ) ≤ ‖modularLambdaH σ‖ :=
          h_cusp1 ⟨h_mem_ball, hσ_im_pos, hσ_re_pos, hσ_re_lt, hσ_semi⟩
        linarith only [h_ge_one, hc_le_half]
  -- ====================================================================
  -- Step 4: choice of the height `T` and the reference point `τ₀`.
  -- ====================================================================
  set T : ℝ := max 3 (Real.log (160000 / c) / Real.pi + 1) with hT_def
  have hT_ge_3 : (3:ℝ) ≤ T := le_max_left _ _
  have hT_ge_log : Real.log (160000 / c) / Real.pi + 1 ≤ T := le_max_right _ _
  set τ₀ : ℂ := ((1/2 : ℝ) : ℂ) + (T : ℂ) * Complex.I with hτ₀_def
  have hτ₀_re : τ₀.re = 1/2 := by
    rw [hτ₀_def]; simp
  have hτ₀_im : τ₀.im = T := by
    rw [hτ₀_def]; simp
  have hτ₀_mem : τ₀ ∈ Gamma2FundamentalDomainInterior := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hτ₀_im]; linarith only [hT_ge_3]
    · rw [hτ₀_re]; norm_num
    · rw [hτ₀_re]; norm_num
    · have h_eq : 2 * τ₀ - 1 = ((2 * T : ℝ) : ℂ) * Complex.I := by
        rw [hτ₀_def]; push_cast; ring
      rw [h_eq, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith only [hT_ge_3] : (0:ℝ) < 2 * T), mul_one]
      linarith only [hT_ge_3]
  -- the q-coordinate size at height T
  set u : ℝ := Real.exp (-(Real.pi * T)) with hu_def
  have hu_pos : 0 < u := Real.exp_pos _
  have h_u_lt : u < 1/10000 := by
    have hmul3 : Real.pi * 3 ≤ Real.pi * T := mul_le_mul_of_nonneg_left hT_ge_3 hπ_pos.le
    have h1 : u ≤ Real.exp (-(Real.pi * 3)) := by
      rw [hu_def]
      exact Real.exp_le_exp.mpr (by linarith only [hmul3])
    have h2 : Real.exp (-(Real.pi * 3)) * Real.exp Real.pi ^ 3 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add,
        show -(Real.pi * 3) + (3:ℕ) * Real.pi = 0 by push_cast; ring]
      exact Real.exp_zero
    have h_mul := mul_lt_mul_of_pos_left h10000 (Real.exp_pos (-(Real.pi * 3)))
    rw [h2] at h_mul
    linarith only [h1, h_mul, Real.exp_pos (-(Real.pi * 3))]
  -- real part of the exponent, and the chart norm identities
  have h_re_pi : ∀ σ : ℂ, ((Real.pi : ℂ) * Complex.I * σ).re = -(Real.pi * σ.im) := by
    intro σ
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h_norm_E1 : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀)‖ = u := by
    rw [Complex.norm_exp, h_re_pi τ₀, hτ₀_im, hu_def]
  have h_E2_eq : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ₀) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h_E3_eq : Complex.exp (3 * (Real.pi : ℂ) * Complex.I * τ₀) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀) ^ 3 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h_norm_E2 : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ₀)‖ = u ^ 2 := by
    rw [h_E2_eq, norm_pow, h_norm_E1]
  have h_norm_E3 : ‖Complex.exp (3 * (Real.pi : ℂ) * Complex.I * τ₀)‖ = u ^ 3 := by
    rw [h_E3_eq, norm_pow, h_norm_E1]
  have h_u4 : Real.exp (-4 * Real.pi * T) = u ^ 4 := by
    rw [hu_def, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- ====================================================================
  -- Step 5: nonvanishing of the derivative at `τ₀`.
  -- ====================================================================
  have h_deriv_ne : deriv modularLambdaH τ₀ ≠ 0 := by
    have h_im_ge_one : 1 ≤ τ₀.im := by rw [hτ₀_im]; linarith only [hT_ge_3]
    have h_bound := modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one h_im_ge_one
    rw [hτ₀_im, h_u4] at h_bound
    -- norms of the three leading terms
    have hA_norm : ‖(16:ℂ) * (Real.pi : ℂ) * Complex.I *
        Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀)‖ = 16 * Real.pi * u := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hπ_pos, h_norm_E1]
      norm_num
    have hB_norm : ‖(256:ℂ) * (Real.pi : ℂ) * Complex.I *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ₀)‖ = 256 * Real.pi * u ^ 2 := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hπ_pos, h_norm_E2]
      norm_num
    have hC_norm : ‖(2112:ℂ) * (Real.pi : ℂ) * Complex.I *
        Complex.exp (3 * (Real.pi : ℂ) * Complex.I * τ₀)‖ = 2112 * Real.pi * u ^ 3 := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hπ_pos, h_norm_E3]
      norm_num
    -- reverse triangle inequality
    have h_tri : ‖(16:ℂ) * (Real.pi : ℂ) * Complex.I *
          Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀)‖ ≤
        ‖deriv modularLambdaH τ₀ -
            16 * (Real.pi : ℂ) * Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀) +
            256 * (Real.pi : ℂ) * Complex.I *
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ₀) -
            2112 * (Real.pi : ℂ) * Complex.I *
              Complex.exp (3 * (Real.pi : ℂ) * Complex.I * τ₀)‖ +
          ‖(256:ℂ) * (Real.pi : ℂ) * Complex.I *
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ₀)‖ +
          ‖(2112:ℂ) * (Real.pi : ℂ) * Complex.I *
              Complex.exp (3 * (Real.pi : ℂ) * Complex.I * τ₀)‖ +
          ‖deriv modularLambdaH τ₀‖ := by
      set D := deriv modularLambdaH τ₀ with hD_def
      set A := (16:ℂ) * (Real.pi : ℂ) * Complex.I *
        Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀) with hA_def
      set B := (256:ℂ) * (Real.pi : ℂ) * Complex.I *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ₀) with hB_def
      set C := (2112:ℂ) * (Real.pi : ℂ) * Complex.I *
        Complex.exp (3 * (Real.pi : ℂ) * Complex.I * τ₀) with hC_def
      have h_eq : A = -(D - A + B - C) + B + (-C) + D := by ring
      calc ‖A‖ = ‖-(D - A + B - C) + B + (-C) + D‖ := by rw [← h_eq]
        _ ≤ ‖-(D - A + B - C) + B + (-C)‖ + ‖D‖ := norm_add_le _ _
        _ ≤ ‖-(D - A + B - C) + B‖ + ‖-C‖ + ‖D‖ := by
            have h := norm_add_le (-(D - A + B - C) + B) (-C)
            linarith only [h]
        _ ≤ ‖-(D - A + B - C)‖ + ‖B‖ + ‖-C‖ + ‖D‖ := by
            have h := norm_add_le (-(D - A + B - C)) B
            linarith only [h]
        _ = ‖D - A + B - C‖ + ‖B‖ + ‖C‖ + ‖D‖ := by rw [norm_neg, norm_neg]
    rw [hA_norm, hB_norm, hC_norm] at h_tri
    have h_norm_lower : 16 * Real.pi * u - 256 * Real.pi * u ^ 2 -
        2112 * Real.pi * u ^ 3 - 100000 * u ^ 4 ≤ ‖deriv modularLambdaH τ₀‖ := by
      linarith only [h_bound, h_tri]
    have h_pos := h_deep_pos Real.pi u hπ_gt3 hπ_lt4 hu_pos h_u_lt
    exact norm_pos_iff.mp (lt_of_lt_of_le h_pos h_norm_lower)
  -- ====================================================================
  -- Step 6: smallness of the reference value: `‖λ(τ₀)‖ < c`.
  -- ====================================================================
  have h_w₀_lt_c : ‖modularLambdaH τ₀‖ < c := by
    have h_im_ge_one : 1 ≤ τ₀.im := by rw [hτ₀_im]; linarith only [hT_ge_3]
    have h_le := modularLambdaH_norm_le_exp_of_im_ge_one h_im_ge_one
    rw [hτ₀_im] at h_le
    have h_exp_eq : Real.exp (-Real.pi * T) = u := by
      rw [hu_def]; congr 1; ring
    rw [h_exp_eq] at h_le
    -- `160000·u < c` from the choice of `T`
    have h_ratio_pos : (0:ℝ) < 160000 / c := div_pos (by norm_num) hc_pos
    have h_log_lt : Real.log (160000 / c) < Real.pi * T := by
      have h1 : Real.log (160000 / c) / Real.pi ≤ T - 1 := by
        linarith only [hT_ge_log]
      have h2 : Real.log (160000 / c) ≤ (T - 1) * Real.pi := (div_le_iff₀ hπ_pos).mp h1
      have h3 : (T - 1) * Real.pi < T * Real.pi :=
        mul_lt_mul_of_pos_right (by linarith only []) hπ_pos
      linarith only [h2, h3]
    have h_lt_exp : 160000 / c < Real.exp (Real.pi * T) :=
      (Real.log_lt_iff_lt_exp h_ratio_pos).mp h_log_lt
    have h_uE : u * Real.exp (Real.pi * T) = 1 := by
      rw [hu_def, ← Real.exp_add,
        show -(Real.pi * T) + Real.pi * T = 0 by ring]
      exact Real.exp_zero
    have h3 : (160000 / c) * u < Real.exp (Real.pi * T) * u :=
      mul_lt_mul_of_pos_right h_lt_exp hu_pos
    rw [mul_comm (Real.exp (Real.pi * T)) u, h_uE] at h3
    have h4 := mul_lt_mul_of_pos_left h3 hc_pos
    rw [mul_one] at h4
    have h5 : c * (160000 / c * u) = 160000 * u := by
      field_simp
    rw [h5] at h4
    linarith only [h_le, h4]
  -- ====================================================================
  -- Step 7: the chart bridging identity.
  -- ====================================================================
  have h_bridge : ∀ σ : ℂ,
      modularLambdaH_cusp (Complex.exp ((Real.pi : ℂ) * Complex.I * σ)) =
        modularLambdaH σ := by
    intro σ
    have h_qe : Function.Periodic.qParam 2 σ =
        Complex.exp ((Real.pi : ℂ) * Complex.I * σ) := by
      unfold Function.Periodic.qParam
      congr 1
      push_cast
      ring
    rw [← h_qe]
    exact modularLambdaH_cusp_qParam σ
  have h_q₀_le : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀)‖ ≤ 1/100 := by
    rw [h_norm_E1]
    linarith only [h_u_lt]
  have h_q₀_mem : Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀) ∈
      Metric.closedBall (0:ℂ) (1/100) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact h_q₀_le
  -- ====================================================================
  -- Step 8: assemble the five conjuncts.
  -- ====================================================================
  refine ⟨modularLambdaH τ₀, τ₀, modularLambdaH_F_im_pos τ₀ hτ₀_mem, hτ₀_mem, rfl,
    h_deriv_ne, ?_⟩
  intro τ hτ_mem hτ_eq
  obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt, hτ_semi⟩ := hτ_mem
  -- every `F^o`-preimage of `w₀` lives above height 2
  have hτ_im_gt : 2 < τ.im := by
    by_contra h_con
    rw [not_lt] at h_con
    have h_low := h_lower τ ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt, hτ_semi⟩ h_con
    rw [hτ_eq] at h_low
    linarith only [h_low, h_w₀_lt_c]
  -- its q-coordinate lies in the small disk
  have h_qτ_norm : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ)‖ =
      Real.exp (-(Real.pi * τ.im)) := by
    rw [Complex.norm_exp, h_re_pi τ]
  have h_qτ_le : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ)‖ ≤ 1/100 := by
    rw [h_qτ_norm]
    have hmul2 : Real.pi * 2 ≤ Real.pi * τ.im :=
      mul_le_mul_of_nonneg_left hτ_im_gt.le hπ_pos.le
    have h1 : Real.exp (-(Real.pi * τ.im)) ≤ Real.exp (-(Real.pi * 2)) :=
      Real.exp_le_exp.mpr (by linarith only [hmul2])
    linarith only [h1, h_exp_2pi_lt]
  have h_qτ_mem : Complex.exp ((Real.pi : ℂ) * Complex.I * τ) ∈
      Metric.closedBall (0:ℂ) (1/100) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact h_qτ_le
  -- equal chart values, hence equal q-coordinates
  have h_vals : modularLambdaH_cusp (Complex.exp ((Real.pi : ℂ) * Complex.I * τ)) =
      modularLambdaH_cusp (Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀)) := by
    rw [h_bridge τ, h_bridge τ₀, hτ_eq]
  have h_q_eq : Complex.exp ((Real.pi : ℂ) * Complex.I * τ) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ₀) :=
    h_cusp_injOn _ h_qτ_mem _ h_q₀_mem h_vals
  -- unwind the exponential equality
  rw [Complex.exp_eq_exp_iff_exists_int] at h_q_eq
  obtain ⟨n, hn⟩ := h_q_eq
  have hπI_ne : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hπ_pos)) Complex.I_ne_zero
  have h_τ_eq : τ = τ₀ + 2 * (n : ℂ) := by
    apply mul_left_cancel₀ hπI_ne
    rw [hn]
    ring
  have h_re_eq : τ.re = 1/2 + 2 * (n:ℝ) := by
    rw [h_τ_eq, Complex.add_re, hτ₀_re]
    simp
  rw [h_re_eq] at hτ_re_pos hτ_re_lt
  have h1 : (n:ℝ) < 1 := by linarith only [hτ_re_lt]
  have h2 : (-1:ℝ) < (n:ℝ) := by linarith only [hτ_re_pos]
  have h1' : n < 1 := by exact_mod_cast h1
  have h2' : (-1:ℤ) < n := by exact_mod_cast h2
  have hn0 : n = 0 := by omega
  rw [h_τ_eq, hn0]
  simp


/-! ## The boundary-integral bridge and the homotopy to the circle -/

set_option maxHeartbeats 400000 in
-- The six-piece chain-rule/substitution conversion is elaboration-heavy.
/-- **Bridge: F_Y boundary integral expression equals image-curve
contour integral.** For valid F_Y parameters with `λ ≠ w` on each of
the six boundary pieces, the six-term AP-derived boundary integral
expression (with the standard CCW orientation signs) coincides with
`Complex.pathContourIntegral (λ ∘ F_Y_boundary_parameterization δ Y R₀)`
of `(z − w)⁻¹` over `[0, 6]`.

Proof: split the `[0, 6]` integral into six segments `[k, k+1]` for
`k = 0, …, 5`. On each segment `F_Y_boundary_parameterization`
restricts to one of the six smooth piece formulas (linear edges or
the semicircle arc). For each piece, apply the chain rule (with the
piece's affine/circle derivative) and substitute the natural parameter
(`x` for horizontal edges, `y` for vertical edges, `θ` for the arc) to
match the corresponding term in the boundary integral. The signs
match: edges traversed in the parameter's positive direction get a
`+`, those in the reverse direction get a `−`, the arc with parameter
`π(2 − t)` reversal gets a `−`. -/
theorem modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
    {w : ℂ} {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0) :
    (∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      (∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
    Complex.pathContourIntegral
      (fun t => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      0 6 (fun z => (z - w)⁻¹) := by
  -- The γ_full integrand.
  set u : ℝ → ℂ := fun t =>
    (modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w)⁻¹ *
      deriv (fun s => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ s)) t
  -- λ facts on ℍ.
  have hH_open : IsOpen {τ : ℂ | 0 < τ.im} :=
    Complex.continuous_im.isOpen_preimage _ isOpen_Ioi
  have h_lam_deriv_cont : ContinuousOn (deriv modularLambdaH) {τ : ℂ | 0 < τ.im} :=
    (modularLambdaH_differentiableOn.analyticOnNhd hH_open).deriv.continuousOn
  have hst : IsScalarTower ℝ ℂ ℂ := IsScalarTower.right
  have hY_pos : 0 < Y := lt_trans hδ hδY
  -- Per-piece engine: a globally differentiable formula matching the boundary
  -- parameterization on `[a, b]`, mapping `[a, b]` into `ℍ`, and avoiding `w`
  -- yields the chain-rule identity for the piece, plus interval-integrability
  -- of the γ_full integrand on the piece.
  have h_piece : ∀ (a b : ℝ) (formula formula' : ℝ → ℂ),
      a ≤ b →
      (∀ t : ℝ, HasDerivAt formula (formula' t) t) →
      Continuous formula' →
      (∀ t ∈ Set.Icc a b, 0 < (formula t).im) →
      (∀ t ∈ Set.Icc a b, F_Y_boundary_parameterization δ Y R₀ t = formula t) →
      (∀ t ∈ Set.Icc a b, modularLambdaH (formula t) - w ≠ 0) →
      ((∫ t in a..b, u t) =
          ∫ t in a..b, (modularLambdaH (formula t) - w)⁻¹ *
            (formula' t • deriv modularLambdaH (formula t))) ∧
        IntervalIntegrable u MeasureTheory.volume a b := by
    intro a b formula formula' hab h_form_d h_form'_cont h_im_pos h_F_eq h_ne
    have h_form_cont : Continuous formula :=
      continuous_iff_continuousAt.mpr fun t => (h_form_d t).continuousAt
    set V : Set ℝ := {t : ℝ | 0 < (formula t).im}
    have hV_open : IsOpen V :=
      (Complex.continuous_im.comp h_form_cont).isOpen_preimage _ isOpen_Ioi
    have h_Icc_V : Set.Icc a b ⊆ V := h_im_pos
    -- Chain rule on V via scomp with explicit scalar-tower instance.
    have h_chain : ∀ t ∈ V, HasDerivAt (fun s => modularLambdaH (formula s))
        (formula' t • deriv modularLambdaH (formula t)) t := by
      intro t ht
      have h_im : 0 < (formula t).im := ht
      have h_lam_d : HasDerivAt modularLambdaH
          (deriv modularLambdaH (formula t)) (formula t) :=
        (modularLambdaH_differentiableAt_of_im_pos h_im).hasDerivAt
      exact @HasDerivAt.scomp ℝ _ ℂ _ _ t ℂ _ _ _ hst _ _ _ _ h_lam_d (h_form_d t)
    have h_g_cont : ContinuousOn
        (fun t => formula' t • deriv modularLambdaH (formula t)) V := by
      refine ContinuousOn.smul h_form'_cont.continuousOn ?_
      refine h_lam_deriv_cont.comp h_form_cont.continuousOn ?_
      intro t ht; exact ht
    have h_deriv_eqOn : Set.EqOn (deriv (fun s => modularLambdaH (formula s)))
        (fun t => formula' t • deriv modularLambdaH (formula t)) V :=
      fun t ht => (h_chain t ht).deriv
    have h_deriv_cont : ContinuousOn
        (deriv (fun s => modularLambdaH (formula s))) V :=
      h_g_cont.congr h_deriv_eqOn
    -- The formula integrand.
    set v : ℝ → ℂ := fun t =>
      (modularLambdaH (formula t) - w)⁻¹ *
        deriv (fun s => modularLambdaH (formula s)) t
    -- v is continuous on the closed piece, hence interval-integrable.
    have h_v_cont : ContinuousOn v (Set.Icc a b) := by
      intro t ht
      have htV : t ∈ V := h_Icc_V ht
      refine ContinuousAt.continuousWithinAt ?_
      have h1 : ContinuousAt (fun s => modularLambdaH (formula s)) t :=
        (h_chain t htV).continuousAt
      have h2 : ContinuousAt (deriv (fun s => modularLambdaH (formula s))) t :=
        h_deriv_cont.continuousAt (hV_open.mem_nhds htV)
      refine ContinuousAt.mul ?_ h2
      refine ContinuousAt.inv₀ (h1.sub continuousAt_const) ?_
      exact h_ne t ht
    have h_v_ii : IntervalIntegrable v MeasureTheory.volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hab]; exact h_v_cont
    -- u = v a.e. on uIoc a b: they can differ only at the corner b.
    have h_ae_imp : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        x ∈ Set.uIoc a b → u x = v x := by
      rw [MeasureTheory.ae_iff]
      refine MeasureTheory.measure_mono_null (t := {b}) ?_
        (MeasureTheory.measure_singleton b)
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      push Not at hx
      obtain ⟨hx_ioc, hx_ne⟩ := hx
      rw [Set.uIoc_of_le hab] at hx_ioc
      rw [Set.mem_singleton_iff]
      by_contra h_xb
      apply hx_ne
      have hx_oo : x ∈ Set.Ioo a b := ⟨hx_ioc.1, lt_of_le_of_ne hx_ioc.2 h_xb⟩
      have hx_icc : x ∈ Set.Icc a b := ⟨le_of_lt hx_oo.1, le_of_lt hx_oo.2⟩
      have h_eq_nbhd :
          (fun s => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ s)) =ᶠ[nhds x]
          (fun s => modularLambdaH (formula s)) := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        refine ⟨Set.Ioo a b, isOpen_Ioo.mem_nhds hx_oo, fun y hy => ?_⟩
        change modularLambdaH (F_Y_boundary_parameterization δ Y R₀ y) =
          modularLambdaH (formula y)
        rw [h_F_eq y ⟨le_of_lt hy.1, le_of_lt hy.2⟩]
      have h_deriv_eq :
          deriv (fun s => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ s)) x =
          deriv (fun s => modularLambdaH (formula s)) x := h_eq_nbhd.deriv_eq
      change (modularLambdaH (F_Y_boundary_parameterization δ Y R₀ x) - w)⁻¹ *
          deriv (fun s => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ s)) x =
        (modularLambdaH (formula x) - w)⁻¹ *
          deriv (fun s => modularLambdaH (formula s)) x
      rw [h_F_eq x hx_icc, h_deriv_eq]
    have h_int_eq : (∫ t in a..b, u t) = ∫ t in a..b, v t :=
      intervalIntegral.integral_congr_ae h_ae_imp
    have h_uv_ae : u =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] v :=
      (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr h_ae_imp
    have h_u_ii : IntervalIntegrable u MeasureTheory.volume a b :=
      h_v_ii.congr_ae h_uv_ae.symm
    -- Rewrite the deriv of the composition via the chain rule on all of [a, b].
    have h_v_to_chain : (∫ t in a..b, v t) =
        ∫ t in a..b, (modularLambdaH (formula t) - w)⁻¹ *
          (formula' t • deriv modularLambdaH (formula t)) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have htV : t ∈ V := h_Icc_V ht
      change (modularLambdaH (formula t) - w)⁻¹ *
          deriv (fun s => modularLambdaH (formula s)) t =
        (modularLambdaH (formula t) - w)⁻¹ *
          (formula' t • deriv modularLambdaH (formula t))
      rw [(h_chain t htV).deriv]
    exact ⟨h_int_eq.trans h_v_to_chain, h_u_ii⟩
  -- Continuity of the horizontal-edge target integrand.
  have h_g_cont_horiz : ∀ (c A B : ℝ), 0 < c →
      (∀ x ∈ Set.Icc A B, modularLambdaH ((x : ℂ) + (c : ℂ) * Complex.I) - w ≠ 0) →
      ContinuousOn (fun s : ℝ => deriv modularLambdaH ((s : ℂ) + (c : ℂ) * Complex.I) /
        (modularLambdaH ((s : ℂ) + (c : ℂ) * Complex.I) - w)) (Set.Icc A B) := by
    intro c A B hc h_ne_c
    have hφ : Continuous (fun s : ℝ => (s : ℂ) + (c : ℂ) * Complex.I) :=
      Complex.continuous_ofReal.add continuous_const
    have h_maps : ∀ s ∈ Set.Icc A B,
        ((s : ℂ) + (c : ℂ) * Complex.I) ∈ {τ : ℂ | 0 < τ.im} := by
      intro s _
      change 0 < ((s : ℂ) + (c : ℂ) * Complex.I).im
      simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re] using hc
    have h_num : ContinuousOn
        (fun s : ℝ => deriv modularLambdaH ((s : ℂ) + (c : ℂ) * Complex.I))
        (Set.Icc A B) := h_lam_deriv_cont.comp hφ.continuousOn h_maps
    have h_den : ContinuousOn
        (fun s : ℝ => modularLambdaH ((s : ℂ) + (c : ℂ) * Complex.I) - w)
        (Set.Icc A B) :=
      (modularLambdaH_differentiableOn.continuousOn.comp hφ.continuousOn h_maps).sub
        continuousOn_const
    exact h_num.div h_den h_ne_c
  -- Continuity of the vertical-edge target integrand.
  have h_g_cont_vert : ∀ (e : ℂ), e.im = 0 →
      (∀ y ∈ Set.Icc δ Y, modularLambdaH (e + (y : ℂ) * Complex.I) - w ≠ 0) →
      ContinuousOn (fun s : ℝ => deriv modularLambdaH (e + (s : ℂ) * Complex.I) /
        (modularLambdaH (e + (s : ℂ) * Complex.I) - w)) (Set.Icc δ Y) := by
    intro e he_im h_ne_e
    have hφ : Continuous (fun s : ℝ => e + (s : ℂ) * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h_maps : ∀ s ∈ Set.Icc δ Y,
        (e + (s : ℂ) * Complex.I) ∈ {τ : ℂ | 0 < τ.im} := by
      intro s hs
      change 0 < (e + (s : ℂ) * Complex.I).im
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, he_im]
      have hs1 : δ ≤ s := hs.1
      nlinarith
    have h_num : ContinuousOn
        (fun s : ℝ => deriv modularLambdaH (e + (s : ℂ) * Complex.I))
        (Set.Icc δ Y) := h_lam_deriv_cont.comp hφ.continuousOn h_maps
    have h_den : ContinuousOn
        (fun s : ℝ => modularLambdaH (e + (s : ℂ) * Complex.I) - w)
        (Set.Icc δ Y) :=
      (modularLambdaH_differentiableOn.continuousOn.comp hφ.continuousOn h_maps).sub
        continuousOn_const
    exact h_num.div h_den h_ne_e
  -- Continuity of the arc target integrand.
  have h_g_arc_cont : ContinuousOn (fun θ : ℝ =>
      deriv modularLambdaH
        (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
      (modularLambdaH
        (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) (Set.Icc 0 Real.pi) := by
    have hφ : Continuous (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) :=
      continuous_circleMap _ _
    have h_maps : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
        _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ ∈
          {τ : ℂ | 0 < τ.im} := by
      intro θ hθ
      have h_cm_im : ∀ (c : ℂ) (R θ' : ℝ),
          (_root_.circleMap c R θ').im = c.im + R * Real.sin θ' := by
        intro c R θ'
        unfold _root_.circleMap
        rw [Complex.exp_mul_I]
        simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im]
      change 0 < (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ).im
      rw [h_cm_im]
      have h_c_im : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im = δ := by
        simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re]
      rw [h_c_im]
      have h_sin_nn : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
      nlinarith [mul_nonneg hR₀_pos.le h_sin_nn]
    have h_num : ContinuousOn (fun θ : ℝ =>
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ))
        (Set.Icc 0 Real.pi) := h_lam_deriv_cont.comp hφ.continuousOn h_maps
    have h_den : ContinuousOn (fun θ : ℝ =>
        modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w)
        (Set.Icc 0 Real.pi) :=
      (modularLambdaH_differentiableOn.continuousOn.comp hφ.continuousOn h_maps).sub
        continuousOn_const
    have h_exp_cont : Continuous
        (fun θ : ℝ => Complex.I * R₀ * Complex.exp (Complex.I * θ)) :=
      continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))
    exact (h_num.div h_den hg_arc).mul h_exp_cont.continuousOn
  -- Piece 0: bottom-left edge.
  have h0_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I)
      ((1 / 2 - R₀ : ℂ)) t := by
    intro t
    have h1 := Complex.ofRealCLM.hasDerivAt (x := t)
    simpa using (h1.mul_const ((1 / 2 - R₀ : ℂ))).add_const ((δ : ℂ) * Complex.I)
  have h0_im : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I).im := by
    intro t _
    simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re] using hδ
  have h0_eq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      F_Y_boundary_parameterization δ Y R₀ t =
      (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I := by
    intro t ht
    unfold F_Y_boundary_parameterization
    rw [if_pos ht.2]
  have h0_ne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0 := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h_pt : (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I =
        ((t * (1 / 2 - R₀) : ℝ) : ℂ) + (δ : ℂ) * Complex.I := by
      push_cast; ring
    rw [h_pt]
    exact hg_bot_left (t * (1 / 2 - R₀)) ⟨by nlinarith, by nlinarith⟩
  obtain ⟨hI0, hII0⟩ := h_piece 0 1
    (fun t : ℝ => (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I)
    (fun _ : ℝ => (1 / 2 - R₀ : ℂ))
    (by norm_num) h0_d continuous_const h0_im h0_eq h0_ne
  have h0_conv : (∫ t in (0 : ℝ)..1, u t) =
      ∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) := by
    have h_f_d : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => t * (1 / 2 - R₀)) ((fun _ : ℝ => 1 / 2 - R₀) x) x :=
      fun x _ => hasDerivAt_mul_const _
    have h_img : (fun t : ℝ => t * (1 / 2 - R₀)) '' Set.uIcc (0 : ℝ) 1 ⊆
        Set.Icc (0 : ℝ) (1 / 2 - R₀) := by
      intro p hp
      obtain ⟨t, ht, h_eq⟩ := hp
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      obtain ⟨ht0, ht1⟩ := ht
      have h_eq' : t * (1 / 2 - R₀) = p := h_eq
      rw [← h_eq']
      exact ⟨by nlinarith, by nlinarith⟩
    have h_subst : (∫ t in (0 : ℝ)..1, (fun _ : ℝ => 1 / 2 - R₀) t •
          ((fun x : ℝ => deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) ∘
            (fun t : ℝ => t * (1 / 2 - R₀))) t) =
        ∫ x in ((0 : ℝ) * (1 / 2 - R₀))..((1 : ℝ) * (1 / 2 - R₀)),
          deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
          (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) :=
      intervalIntegral.integral_deriv_smul_comp' h_f_d continuousOn_const
        ((h_g_cont_horiz δ 0 (1 / 2 - R₀) hδ hg_bot_left).mono h_img)
    calc (∫ t in (0 : ℝ)..1, u t)
        = ∫ t in (0 : ℝ)..1,
            (modularLambdaH ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I) - w)⁻¹ *
              ((1 / 2 - R₀ : ℂ) *
                deriv modularLambdaH ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I)) := hI0
      _ = ∫ t in (0 : ℝ)..1, (fun _ : ℝ => 1 / 2 - R₀) t •
            ((fun x : ℝ => deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
              (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) ∘
              (fun t : ℝ => t * (1 / 2 - R₀))) t := by
          refine intervalIntegral.integral_congr ?_
          intro t _
          change (modularLambdaH ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I) - w)⁻¹ *
              ((1 / 2 - R₀ : ℂ) *
                deriv modularLambdaH ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I)) =
            (1 / 2 - R₀ : ℝ) •
              (deriv modularLambdaH (((t * (1 / 2 - R₀) : ℝ) : ℂ) + (δ : ℂ) * Complex.I) /
                (modularLambdaH (((t * (1 / 2 - R₀) : ℝ) : ℂ) + (δ : ℂ) * Complex.I) - w))
          rw [Complex.real_smul]
          push_cast
          ring
      _ = ∫ x in ((0 : ℝ) * (1 / 2 - R₀))..((1 : ℝ) * (1 / 2 - R₀)),
            deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) := h_subst
      _ = ∫ x in (0 : ℝ)..(1 / 2 - R₀),
            deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) := by
          rw [zero_mul, one_mul]
  -- Piece 1: semicircular arc.
  have h1_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (Real.pi * (2 - t)))
      ((Real.pi * -1 : ℝ) •
        (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I)) t := by
    intro t
    have h_inner : HasDerivAt (fun s : ℝ => Real.pi * (2 - s)) (Real.pi * -1) t := by
      have h := ((hasDerivAt_id t).const_sub (2 : ℝ)).const_mul Real.pi
      simpa using h
    have h_outer := hasDerivAt_circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (Real.pi * (2 - t))
    have h_comp := h_outer.scomp t h_inner
    simpa [Function.comp_def] using! h_comp
  have h1_cont : Continuous (fun t : ℝ => (Real.pi * -1 : ℝ) •
      (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I)) := by
    refine Continuous.fun_const_smul ?_ _
    refine Continuous.mul ?_ continuous_const
    exact (continuous_circleMap 0 R₀).comp (by fun_prop)
  have h1_im : ∀ t ∈ Set.Icc (1 : ℝ) 2,
      0 < (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (Real.pi * (2 - t))).im := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have h_cm_im : ∀ (c : ℂ) (R θ : ℝ),
        (_root_.circleMap c R θ).im = c.im + R * Real.sin θ := by
      intro c R θ
      unfold _root_.circleMap
      rw [Complex.exp_mul_I]
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im]
    rw [h_cm_im]
    have h_c_im : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im = δ := by
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
    rw [h_c_im]
    have h_sin_nn : 0 ≤ Real.sin (Real.pi * (2 - t)) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
      · have h2t : (0 : ℝ) ≤ 2 - t := by linarith
        positivity
      · nlinarith [Real.pi_pos]
    nlinarith [mul_nonneg hR₀_pos.le h_sin_nn]
  have h1_eq : ∀ t ∈ Set.Icc (1 : ℝ) 2,
      F_Y_boundary_parameterization δ Y R₀ t =
      _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t)) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    unfold F_Y_boundary_parameterization
    rcases eq_or_lt_of_le ht1 with h_eq | h_lt
    · -- t = 1: junction with piece 0.
      rw [← h_eq]
      rw [if_pos (le_refl 1)]
      unfold _root_.circleMap
      have h_angle : ((Real.pi * (2 - 1) : ℝ) : ℂ) * Complex.I =
          (Real.pi : ℂ) * Complex.I := by push_cast; ring
      rw [h_angle, Complex.exp_pi_mul_I]
      push_cast; ring
    · rw [if_neg (not_le.mpr h_lt), if_pos ht2]
  have h1_ne : ∀ t ∈ Set.Icc (1 : ℝ) 2,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (Real.pi * (2 - t))) - w ≠ 0 := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    refine hg_arc (Real.pi * (2 - t)) ⟨?_, ?_⟩
    · exact mul_nonneg Real.pi_pos.le (by linarith)
    · nlinarith [Real.pi_pos]
  obtain ⟨hI1, hII1⟩ := h_piece 1 2
    (fun t : ℝ => _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (Real.pi * (2 - t)))
    (fun t : ℝ => (Real.pi * -1 : ℝ) •
      (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I))
    (by norm_num) h1_d h1_cont h1_im h1_eq h1_ne
  have h1_conv : (∫ t in (1 : ℝ)..2, u t) =
      -∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)) := by
    have h_f_d : ∀ x ∈ Set.uIcc (1 : ℝ) 2,
        HasDerivAt (fun t : ℝ => Real.pi * (2 - t)) ((fun _ : ℝ => Real.pi * -1) x) x := by
      intro x _
      simpa using ((hasDerivAt_id x).const_sub (2 : ℝ)).const_mul Real.pi
    have h_img : (fun t : ℝ => Real.pi * (2 - t)) '' Set.uIcc (1 : ℝ) 2 ⊆
        Set.Icc (0 : ℝ) Real.pi := by
      intro p hp
      obtain ⟨t, ht, h_eq⟩ := hp
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
      obtain ⟨ht1, ht2⟩ := ht
      have h_eq' : Real.pi * (2 - t) = p := h_eq
      rw [← h_eq']
      constructor
      · exact mul_nonneg Real.pi_pos.le (by linarith)
      · nlinarith [Real.pi_pos]
    have h_cm : ∀ θ : ℝ, _root_.circleMap 0 R₀ θ * Complex.I =
        Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
      intro θ
      unfold _root_.circleMap
      rw [mul_comm ((θ : ℝ) : ℂ) Complex.I]
      ring
    have h_subst : (∫ t in (1 : ℝ)..2, (fun _ : ℝ => Real.pi * -1) t •
          ((fun θ : ℝ =>
            deriv modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
            (modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
            (Complex.I * R₀ * Complex.exp (Complex.I * θ))) ∘
            (fun t : ℝ => Real.pi * (2 - t))) t) =
        ∫ θ in (Real.pi * (2 - 1))..(Real.pi * (2 - 2)),
          deriv modularLambdaH
            (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
          (modularLambdaH
            (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ)) :=
      intervalIntegral.integral_deriv_smul_comp' h_f_d continuousOn_const
        (h_g_arc_cont.mono h_img)
    calc (∫ t in (1 : ℝ)..2, u t)
        = ∫ t in (1 : ℝ)..2,
            (modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
              (Real.pi * (2 - t))) - w)⁻¹ *
              (((Real.pi * -1 : ℝ) •
                (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I)) *
                deriv modularLambdaH (_root_.circleMap
                  ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t)))) := hI1
      _ = ∫ t in (1 : ℝ)..2, (fun _ : ℝ => Real.pi * -1) t •
            ((fun θ : ℝ =>
              deriv modularLambdaH
                (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
              (modularLambdaH
                (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
              (Complex.I * R₀ * Complex.exp (Complex.I * θ))) ∘
              (fun t : ℝ => Real.pi * (2 - t))) t := by
          refine intervalIntegral.integral_congr ?_
          intro t _
          change (modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
              (Real.pi * (2 - t))) - w)⁻¹ *
              (((Real.pi * -1 : ℝ) •
                (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I)) *
                deriv modularLambdaH (_root_.circleMap
                  ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t)))) =
            (Real.pi * -1 : ℝ) •
              (deriv modularLambdaH (_root_.circleMap
                ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t))) /
              (modularLambdaH (_root_.circleMap
                ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t))) - w) *
              (Complex.I * R₀ * Complex.exp (Complex.I * ((Real.pi * (2 - t) : ℝ) : ℂ))))
          rw [h_cm (Real.pi * (2 - t)), Complex.real_smul, Complex.real_smul]
          push_cast
          ring
      _ = ∫ θ in (Real.pi * (2 - 1))..(Real.pi * (2 - 2)),
            deriv modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
            (modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
            (Complex.I * R₀ * Complex.exp (Complex.I * θ)) := h_subst
      _ = ∫ θ in Real.pi..(0 : ℝ),
            deriv modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
            (modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
            (Complex.I * R₀ * Complex.exp (Complex.I * θ)) := by
          rw [show Real.pi * (2 - 1) = Real.pi from by ring,
            show Real.pi * (2 - 2) = 0 from by ring]
      _ = -∫ θ in (0 : ℝ)..Real.pi,
            deriv modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
            (modularLambdaH
              (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
            (Complex.I * R₀ * Complex.exp (Complex.I * θ)) :=
          intervalIntegral.integral_symm 0 Real.pi
  -- Piece 2: bottom-right edge.
  have h2_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I)
      ((1 / 2 - R₀ : ℂ)) t := by
    intro t
    have h1 := Complex.ofRealCLM.hasDerivAt (x := t)
    have h2 := (((h1.sub_const (2 : ℂ)).mul_const ((1 / 2 - R₀ : ℂ))).const_add
      ((1 / 2 + R₀ : ℂ))).add_const ((δ : ℂ) * Complex.I)
    simpa using h2
  have h2_im : ∀ t ∈ Set.Icc (2 : ℝ) 3,
      0 < ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I).im := by
    intro t _
    simpa [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.sub_re, Complex.I_im, Complex.I_re] using hδ
  have h2_eq : ∀ t ∈ Set.Icc (2 : ℝ) 3,
      F_Y_boundary_parameterization δ Y R₀ t =
      (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I := by
    intro t ht
    obtain ⟨ht2, ht3⟩ := ht
    unfold F_Y_boundary_parameterization
    have h_not1 : ¬ t ≤ 1 := by linarith
    rcases eq_or_lt_of_le ht2 with h_eq | h_lt
    · -- t = 2: junction with the arc piece.
      rw [← h_eq]
      rw [if_neg (by norm_num : ¬ (2 : ℝ) ≤ 1), if_pos (le_refl (2 : ℝ))]
      unfold _root_.circleMap
      have h_angle : ((Real.pi * (2 - 2) : ℝ) : ℂ) * Complex.I = 0 := by
        push_cast; ring
      rw [h_angle, Complex.exp_zero]
      push_cast; ring
    · rw [if_neg h_not1, if_neg (not_le.mpr h_lt), if_pos ht3]
  have h2_ne : ∀ t ∈ Set.Icc (2 : ℝ) 3,
      modularLambdaH ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) +
        (δ : ℂ) * Complex.I) - w ≠ 0 := by
    intro t ht
    obtain ⟨ht2, ht3⟩ := ht
    have h_pt : (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I =
        ((1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀) : ℝ) : ℂ) + (δ : ℂ) * Complex.I := by
      push_cast; ring
    rw [h_pt]
    exact hg_bot_right (1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀)) ⟨by nlinarith, by nlinarith⟩
  obtain ⟨hI2, hII2⟩ := h_piece 2 3
    (fun t : ℝ => (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I)
    (fun _ : ℝ => (1 / 2 - R₀ : ℂ))
    (by norm_num) h2_d continuous_const h2_im h2_eq h2_ne
  have h2_conv : (∫ t in (2 : ℝ)..3, u t) =
      ∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) := by
    have h_f_d : ∀ x ∈ Set.uIcc (2 : ℝ) 3,
        HasDerivAt (fun t : ℝ => 1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀))
          ((fun _ : ℝ => 1 / 2 - R₀) x) x := by
      intro x _
      simpa using (((hasDerivAt_id x).sub_const (2 : ℝ)).mul_const
        (1 / 2 - R₀)).const_add (1 / 2 + R₀)
    have h_img : (fun t : ℝ => 1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀)) ''
        Set.uIcc (2 : ℝ) 3 ⊆ Set.Icc (1 / 2 + R₀ : ℝ) 1 := by
      intro p hp
      obtain ⟨t, ht, h_eq⟩ := hp
      rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at ht
      obtain ⟨ht2, ht3⟩ := ht
      have h_eq' : 1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀) = p := h_eq
      rw [← h_eq']
      exact ⟨by nlinarith, by nlinarith⟩
    have h_subst : (∫ t in (2 : ℝ)..3, (fun _ : ℝ => 1 / 2 - R₀) t •
          ((fun x : ℝ => deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) ∘
            (fun t : ℝ => 1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀))) t) =
        ∫ x in (1 / 2 + R₀ + ((2 : ℝ) - 2) * (1 / 2 - R₀))..(1 / 2 + R₀ +
            ((3 : ℝ) - 2) * (1 / 2 - R₀)),
          deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
          (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) :=
      intervalIntegral.integral_deriv_smul_comp' h_f_d continuousOn_const
        ((h_g_cont_horiz δ (1 / 2 + R₀) 1 hδ hg_bot_right).mono h_img)
    calc (∫ t in (2 : ℝ)..3, u t)
        = ∫ t in (2 : ℝ)..3,
            (modularLambdaH ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) +
              (δ : ℂ) * Complex.I) - w)⁻¹ *
              ((1 / 2 - R₀ : ℂ) *
                deriv modularLambdaH ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) +
                  (δ : ℂ) * Complex.I)) := hI2
      _ = ∫ t in (2 : ℝ)..3, (fun _ : ℝ => 1 / 2 - R₀) t •
            ((fun x : ℝ => deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
              (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) ∘
              (fun t : ℝ => 1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀))) t := by
          refine intervalIntegral.integral_congr ?_
          intro t _
          change (modularLambdaH ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) +
              (δ : ℂ) * Complex.I) - w)⁻¹ *
              ((1 / 2 - R₀ : ℂ) *
                deriv modularLambdaH ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) +
                  (δ : ℂ) * Complex.I)) =
            (1 / 2 - R₀ : ℝ) •
              (deriv modularLambdaH
                (((1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀) : ℝ) : ℂ) + (δ : ℂ) * Complex.I) /
                (modularLambdaH
                  (((1 / 2 + R₀ + (t - 2) * (1 / 2 - R₀) : ℝ) : ℂ) +
                    (δ : ℂ) * Complex.I) - w))
          rw [Complex.real_smul]
          push_cast
          ring
      _ = ∫ x in (1 / 2 + R₀ + ((2 : ℝ) - 2) * (1 / 2 - R₀))..(1 / 2 + R₀ +
            ((3 : ℝ) - 2) * (1 / 2 - R₀)),
            deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) := h_subst
      _ = ∫ x in (1 / 2 + R₀ : ℝ)..1,
            deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w) := by
          rw [show 1 / 2 + R₀ + ((2 : ℝ) - 2) * (1 / 2 - R₀) = 1 / 2 + R₀ from by ring,
            show 1 / 2 + R₀ + ((3 : ℝ) - 2) * (1 / 2 - R₀) = 1 from by ring]
  -- Piece 3: right edge.
  have h3_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I)
      (((Y - δ : ℂ)) * Complex.I) t := by
    intro t
    have h1 := Complex.ofRealCLM.hasDerivAt (x := t)
    have h2 := ((((h1.sub_const (3 : ℂ)).mul_const ((Y - δ : ℂ))).const_add
      ((δ : ℂ))).mul_const Complex.I).const_add (1 : ℂ)
    simpa using h2
  have h3_im : ∀ t ∈ Set.Icc (3 : ℝ) 4,
      0 < ((1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I).im := by
    intro t ht
    obtain ⟨ht3, ht4⟩ := ht
    simp [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.sub_re, Complex.I_im, Complex.I_re]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ t - 3) (by linarith : (0:ℝ) ≤ Y - δ)]
  have h3_eq : ∀ t ∈ Set.Icc (3 : ℝ) 4,
      F_Y_boundary_parameterization δ Y R₀ t =
      (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I := by
    intro t ht
    obtain ⟨ht3, ht4⟩ := ht
    unfold F_Y_boundary_parameterization
    have h_not1 : ¬ t ≤ 1 := by linarith
    have h_not2 : ¬ t ≤ 2 := by linarith
    rcases eq_or_lt_of_le ht3 with h_eq | h_lt
    · -- t = 3: junction with the bottom-right edge.
      rw [← h_eq]
      rw [if_neg (by norm_num : ¬ (3 : ℝ) ≤ 1), if_neg (by norm_num : ¬ (3 : ℝ) ≤ 2),
        if_pos (le_refl (3 : ℝ))]
      push_cast; ring
    · rw [if_neg h_not1, if_neg h_not2, if_neg (not_le.mpr h_lt), if_pos ht4]
  have h3_ne : ∀ t ∈ Set.Icc (3 : ℝ) 4,
      modularLambdaH ((1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I) - w ≠ 0 := by
    intro t ht
    obtain ⟨ht3, ht4⟩ := ht
    have h_pt : (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I =
        (1 : ℂ) + ((δ + (t - 3) * (Y - δ) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h_pt]
    exact hg_right (δ + (t - 3) * (Y - δ)) ⟨by nlinarith, by nlinarith⟩
  obtain ⟨hI3, hII3⟩ := h_piece 3 4
    (fun t : ℝ => (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I)
    (fun _ : ℝ => ((Y - δ : ℂ)) * Complex.I)
    (by norm_num) h3_d continuous_const h3_im h3_eq h3_ne
  have h3_conv : (∫ t in (3 : ℝ)..4, u t) =
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) := by
    have h_f_d : ∀ x ∈ Set.uIcc (3 : ℝ) 4,
        HasDerivAt (fun t : ℝ => δ + (t - 3) * (Y - δ)) ((fun _ : ℝ => Y - δ) x) x := by
      intro x _
      simpa using (((hasDerivAt_id x).sub_const (3 : ℝ)).mul_const (Y - δ)).const_add δ
    have h_img : (fun t : ℝ => δ + (t - 3) * (Y - δ)) '' Set.uIcc (3 : ℝ) 4 ⊆
        Set.Icc δ Y := by
      intro p hp
      obtain ⟨t, ht, h_eq⟩ := hp
      rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at ht
      obtain ⟨ht3, ht4⟩ := ht
      have h_eq' : δ + (t - 3) * (Y - δ) = p := h_eq
      rw [← h_eq']
      exact ⟨by nlinarith, by nlinarith⟩
    have h_subst : (∫ t in (3 : ℝ)..4, (fun _ : ℝ => Y - δ) t •
          ((fun y : ℝ => deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) ∘
            (fun t : ℝ => δ + (t - 3) * (Y - δ))) t) =
        ∫ y in (δ + ((3 : ℝ) - 3) * (Y - δ))..(δ + ((4 : ℝ) - 3) * (Y - δ)),
          deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
          (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w) :=
      intervalIntegral.integral_deriv_smul_comp' h_f_d continuousOn_const
        ((h_g_cont_vert 1 Complex.one_im hg_right).mono h_img)
    calc (∫ t in (3 : ℝ)..4, u t)
        = ∫ t in (3 : ℝ)..4,
            (modularLambdaH ((1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I) - w)⁻¹ *
              ((Y - δ : ℂ) * Complex.I *
                deriv modularLambdaH ((1 : ℂ) +
                  ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I)) := hI3
      _ = ∫ t in (3 : ℝ)..4, Complex.I *
            ((fun _ : ℝ => Y - δ) t •
              ((fun y : ℝ => deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
                (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) ∘
                (fun t : ℝ => δ + (t - 3) * (Y - δ))) t) := by
          refine intervalIntegral.integral_congr ?_
          intro t _
          change (modularLambdaH ((1 : ℂ) +
              ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I) - w)⁻¹ *
              ((Y - δ : ℂ) * Complex.I *
                deriv modularLambdaH ((1 : ℂ) +
                  ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I)) =
            Complex.I * ((Y - δ : ℝ) •
              (deriv modularLambdaH ((1 : ℂ) +
                ((δ + (t - 3) * (Y - δ) : ℝ) : ℂ) * Complex.I) /
              (modularLambdaH ((1 : ℂ) +
                ((δ + (t - 3) * (Y - δ) : ℝ) : ℂ) * Complex.I) - w)))
          rw [Complex.real_smul]
          push_cast
          ring
      _ = Complex.I * ∫ t in (3 : ℝ)..4,
            (fun _ : ℝ => Y - δ) t •
              ((fun y : ℝ => deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
                (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) ∘
                (fun t : ℝ => δ + (t - 3) * (Y - δ))) t :=
          intervalIntegral.integral_const_mul Complex.I _
      _ = Complex.I * ∫ y in (δ + ((3 : ℝ) - 3) * (Y - δ))..(δ + ((4 : ℝ) - 3) * (Y - δ)),
            deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w) := by
          rw [h_subst]
      _ = Complex.I * (∫ y in (δ : ℝ)..Y,
            deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) := by
          rw [show δ + ((3 : ℝ) - 3) * (Y - δ) = δ from by ring,
            show δ + ((4 : ℝ) - 3) * (Y - δ) = Y from by ring]
  -- Piece 4: top edge.
  have h4_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => ((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I)
      (((-1 : ℝ) : ℂ)) t := by
    intro t
    have h_inner : HasDerivAt (fun s : ℝ => 5 - s) (-1) t :=
      (hasDerivAt_id t).const_sub 5
    exact (h_inner.ofReal_comp).add_const ((Y : ℂ) * Complex.I)
  have h4_im : ∀ t ∈ Set.Icc (4 : ℝ) 5,
      0 < (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I).im := by
    intro t _
    simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re] using hY_pos
  have h4_eq : ∀ t ∈ Set.Icc (4 : ℝ) 5,
      F_Y_boundary_parameterization δ Y R₀ t =
      ((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I := by
    intro t ht
    obtain ⟨ht4, ht5⟩ := ht
    unfold F_Y_boundary_parameterization
    have h_not1 : ¬ t ≤ 1 := by linarith
    have h_not2 : ¬ t ≤ 2 := by linarith
    have h_not3 : ¬ t ≤ 3 := by linarith
    rcases eq_or_lt_of_le ht4 with h_eq | h_lt
    · -- t = 4: junction with the right edge.
      rw [← h_eq]
      rw [if_neg (by norm_num : ¬ (4 : ℝ) ≤ 1), if_neg (by norm_num : ¬ (4 : ℝ) ≤ 2),
        if_neg (by norm_num : ¬ (4 : ℝ) ≤ 3), if_pos (le_refl (4 : ℝ))]
      push_cast; ring
    · rw [if_neg h_not1, if_neg h_not2, if_neg h_not3, if_neg (not_le.mpr h_lt),
        if_pos ht5]
  have h4_ne : ∀ t ∈ Set.Icc (4 : ℝ) 5,
      modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0 := by
    intro t ht
    obtain ⟨ht4, ht5⟩ := ht
    exact hg_top (5 - t) ⟨by linarith, by linarith⟩
  obtain ⟨hI4, hII4⟩ := h_piece 4 5
    (fun t : ℝ => ((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I)
    (fun _ : ℝ => ((-1 : ℝ) : ℂ))
    (by norm_num) h4_d continuous_const h4_im h4_eq h4_ne
  have h4_conv : (∫ t in (4 : ℝ)..5, u t) =
      -∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w) := by
    have h_f_d : ∀ x ∈ Set.uIcc (4 : ℝ) 5,
        HasDerivAt (fun t : ℝ => 5 - t) ((fun _ : ℝ => (-1 : ℝ)) x) x := by
      intro x _
      simpa using (hasDerivAt_id x).const_sub (5 : ℝ)
    have h_img : (fun t : ℝ => 5 - t) '' Set.uIcc (4 : ℝ) 5 ⊆
        Set.Icc (0 : ℝ) 1 := by
      intro p hp
      obtain ⟨t, ht, h_eq⟩ := hp
      rw [Set.uIcc_of_le (by norm_num : (4 : ℝ) ≤ 5)] at ht
      obtain ⟨ht4, ht5⟩ := ht
      have h_eq' : 5 - t = p := h_eq
      rw [← h_eq']
      exact ⟨by linarith, by linarith⟩
    have h_subst : (∫ t in (4 : ℝ)..5, (fun _ : ℝ => (-1 : ℝ)) t •
          ((fun x : ℝ => deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) ∘
            (fun t : ℝ => 5 - t)) t) =
        ∫ x in ((5 : ℝ) - 4)..((5 : ℝ) - 5),
          deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
          (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w) :=
      intervalIntegral.integral_deriv_smul_comp' h_f_d continuousOn_const
        ((h_g_cont_horiz Y 0 1 hY_pos hg_top).mono h_img)
    calc (∫ t in (4 : ℝ)..5, u t)
        = ∫ t in (4 : ℝ)..5,
            (modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I) - w)⁻¹ *
              (((-1 : ℝ) : ℂ) *
                deriv modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I)) := hI4
      _ = ∫ t in (4 : ℝ)..5, (fun _ : ℝ => (-1 : ℝ)) t •
            ((fun x : ℝ => deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
              (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) ∘
              (fun t : ℝ => 5 - t)) t := by
          refine intervalIntegral.integral_congr ?_
          intro t _
          change (modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I) - w)⁻¹ *
              (((-1 : ℝ) : ℂ) *
                deriv modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I)) =
            (-1 : ℝ) •
              (deriv modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I) /
                (modularLambdaH (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I) - w))
          rw [Complex.real_smul]
          push_cast
          ring
      _ = ∫ x in ((5 : ℝ) - 4)..((5 : ℝ) - 5),
            deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w) := h_subst
      _ = ∫ x in (1 : ℝ)..(0 : ℝ),
            deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w) := by
          rw [show (5 : ℝ) - 4 = 1 from by norm_num,
            show (5 : ℝ) - 5 = 0 from by norm_num]
      _ = -∫ x in (0 : ℝ)..1,
            deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
            (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w) :=
          intervalIntegral.integral_symm 0 1
  -- Piece 5: left edge.
  have h5_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I)
      (((-(Y - δ) : ℝ) : ℂ) * Complex.I) t := by
    intro t
    have h_inner : HasDerivAt (fun s : ℝ => Y - (s - 5) * (Y - δ)) (-(Y - δ)) t := by
      have h := (((hasDerivAt_id t).sub_const (5 : ℝ)).mul_const (Y - δ)).const_sub Y
      simpa using h
    exact (h_inner.ofReal_comp).mul_const Complex.I
  have h5_im : ∀ t ∈ Set.Icc (5 : ℝ) 6,
      0 < (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I).im := by
    intro t ht
    obtain ⟨ht5, ht6⟩ := ht
    simp [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    have h_le_one : t - 5 ≤ 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h_le_one (by linarith : (0:ℝ) ≤ Y - δ)]
  have h5_eq : ∀ t ∈ Set.Icc (5 : ℝ) 6,
      F_Y_boundary_parameterization δ Y R₀ t =
      ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I := by
    intro t ht
    obtain ⟨ht5, ht6⟩ := ht
    unfold F_Y_boundary_parameterization
    have h_not1 : ¬ t ≤ 1 := by linarith
    have h_not2 : ¬ t ≤ 2 := by linarith
    have h_not3 : ¬ t ≤ 3 := by linarith
    have h_not4 : ¬ t ≤ 4 := by linarith
    rcases eq_or_lt_of_le ht5 with h_eq | h_lt
    · -- t = 5: junction with the top edge.
      rw [← h_eq]
      rw [if_neg (by norm_num : ¬ (5 : ℝ) ≤ 1), if_neg (by norm_num : ¬ (5 : ℝ) ≤ 2),
        if_neg (by norm_num : ¬ (5 : ℝ) ≤ 3), if_neg (by norm_num : ¬ (5 : ℝ) ≤ 4),
        if_pos (le_refl (5 : ℝ))]
      push_cast; ring
    · rw [if_neg h_not1, if_neg h_not2, if_neg h_not3, if_neg h_not4,
        if_neg (not_le.mpr h_lt), if_pos ht6]
  have h5_ne : ∀ t ∈ Set.Icc (5 : ℝ) 6,
      modularLambdaH (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I) - w ≠ 0 := by
    intro t ht
    obtain ⟨ht5, ht6⟩ := ht
    have h := hg_left (Y - (t - 5) * (Y - δ)) ⟨by nlinarith, by nlinarith⟩
    rwa [zero_add] at h
  obtain ⟨hI5, hII5⟩ := h_piece 5 6
    (fun t : ℝ => ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I)
    (fun _ : ℝ => ((-(Y - δ) : ℝ) : ℂ) * Complex.I)
    (by norm_num) h5_d continuous_const h5_im h5_eq h5_ne
  have h5_conv : (∫ t in (5 : ℝ)..6, u t) =
      Complex.I * -(∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) := by
    have h_f_d : ∀ x ∈ Set.uIcc (5 : ℝ) 6,
        HasDerivAt (fun t : ℝ => Y - (t - 5) * (Y - δ))
          ((fun _ : ℝ => -(Y - δ)) x) x := by
      intro x _
      simpa using (((hasDerivAt_id x).sub_const (5 : ℝ)).mul_const (Y - δ)).const_sub Y
    have h_img : (fun t : ℝ => Y - (t - 5) * (Y - δ)) '' Set.uIcc (5 : ℝ) 6 ⊆
        Set.Icc δ Y := by
      intro p hp
      obtain ⟨t, ht, h_eq⟩ := hp
      rw [Set.uIcc_of_le (by norm_num : (5 : ℝ) ≤ 6)] at ht
      obtain ⟨ht5, ht6⟩ := ht
      have h_eq' : Y - (t - 5) * (Y - δ) = p := h_eq
      rw [← h_eq']
      exact ⟨by nlinarith, by nlinarith⟩
    have h_subst : (∫ t in (5 : ℝ)..6, (fun _ : ℝ => -(Y - δ)) t •
          ((fun y : ℝ => deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) ∘
            (fun t : ℝ => Y - (t - 5) * (Y - δ))) t) =
        ∫ y in (Y - ((5 : ℝ) - 5) * (Y - δ))..(Y - ((6 : ℝ) - 5) * (Y - δ)),
          deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
          (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w) :=
      intervalIntegral.integral_deriv_smul_comp' h_f_d continuousOn_const
        ((h_g_cont_vert 0 Complex.zero_im hg_left).mono h_img)
    calc (∫ t in (5 : ℝ)..6, u t)
        = ∫ t in (5 : ℝ)..6,
            (modularLambdaH (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I) - w)⁻¹ *
              ((((-(Y - δ) : ℝ) : ℂ) * Complex.I) *
                deriv modularLambdaH
                  (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I)) := hI5
      _ = ∫ t in (5 : ℝ)..6, Complex.I *
            ((fun _ : ℝ => -(Y - δ)) t •
              ((fun y : ℝ => deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
                (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) ∘
                (fun t : ℝ => Y - (t - 5) * (Y - δ))) t) := by
          refine intervalIntegral.integral_congr ?_
          intro t _
          change (modularLambdaH (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I) - w)⁻¹ *
              ((((-(Y - δ) : ℝ) : ℂ) * Complex.I) *
                deriv modularLambdaH
                  (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I)) =
            Complex.I * ((-(Y - δ) : ℝ) •
              (deriv modularLambdaH ((0 : ℂ) +
                ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I) /
              (modularLambdaH ((0 : ℂ) +
                ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I) - w)))
          rw [zero_add (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I),
            Complex.real_smul]
          push_cast
          ring
      _ = Complex.I * ∫ t in (5 : ℝ)..6,
            (fun _ : ℝ => -(Y - δ)) t •
              ((fun y : ℝ => deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
                (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) ∘
                (fun t : ℝ => Y - (t - 5) * (Y - δ))) t :=
          intervalIntegral.integral_const_mul Complex.I _
      _ = Complex.I * ∫ y in (Y - ((5 : ℝ) - 5) * (Y - δ))..(Y - ((6 : ℝ) - 5) * (Y - δ)),
            deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w) := by
          rw [h_subst]
      _ = Complex.I * ∫ y in Y..(δ : ℝ),
            deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w) := by
          rw [show Y - ((5 : ℝ) - 5) * (Y - δ) = Y from by ring,
            show Y - ((6 : ℝ) - 5) * (Y - δ) = δ from by ring]
      _ = Complex.I * -(∫ y in (δ : ℝ)..Y,
            deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
            (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) := by
          rw [intervalIntegral.integral_symm δ Y]
  -- Telescope the six pieces.
  have e01 := intervalIntegral.integral_add_adjacent_intervals hII0 hII1
  have hII02 := hII0.trans hII1
  have e02 := intervalIntegral.integral_add_adjacent_intervals hII02 hII2
  have hII03 := hII02.trans hII2
  have e03 := intervalIntegral.integral_add_adjacent_intervals hII03 hII3
  have hII04 := hII03.trans hII3
  have e04 := intervalIntegral.integral_add_adjacent_intervals hII04 hII4
  have hII05 := hII04.trans hII4
  have e05 := intervalIntegral.integral_add_adjacent_intervals hII05 hII5
  unfold Complex.pathContourIntegral
  change _ = ∫ t in (0 : ℝ)..6, u t
  rw [← e05, ← e04, ← e03, ← e02, ← e01,
    h0_conv, h1_conv, h2_conv, h3_conv, h4_conv, h5_conv]
  ring


/-- **Continuous-homotopy invariance of the boundary contour integral.**
Given a continuous closed homotopy `H : [0, 1] × [0, 6] → ℂ \ {w}`
(in the sense of `image_curve_lambda_F_Y_homotopic_to_circle`) between
the image curve `λ ∘ F_Y_boundary_parameterization δ Y R₀` at `s = 0`
and the parameterized CCW circle `circleMap w ε (· · π/3)` at `s = 1`,
the pathContourIntegrals of `(z − w)⁻¹` along the two endpoints are
equal.

This is the load-bearing topological sub-claim. The proof factors
through three pieces:

1. `continuous_log_lift_param_of_continuous_ne_zero` (PathWinding/LogLiftHomotopy.lean):
   a jointly continuous log lift `L` of `H − w` over the homotopy
   rectangle `[0, 1] × [0, 6]`.

2. The integer-continuity argument: the cross-section boundary
   difference `τ s := L s 6 − L s 0` is continuous in `s` and satisfies
   `exp (τ s) = 1` by closedness of `H s`, hence takes values in
   `2πi · ℤ`; by the intermediate value theorem applied to
   `s ↦ (τ s).im / (2π)`, the endpoint values agree: `τ 0 = τ 1`.

3. The FTC bridges (PathWinding/): at `s = 0`, the piecewise-C¹
   bridge `pathContourIntegral_inv_eq_log_lift_diff_F_Y_image_curve`
   identifies the image-curve contour integral with `τ 0`; at `s = 1`,
   the C¹ bridge `pathContourIntegral_inv_eq_log_lift_diff_of_contDiff`
   identifies the circle contour integral with `τ 1`. -/
theorem modularLambdaH_F_Y_image_curve_pathContourIntegral_eq_circle_via_homotopy
    {w : ℂ} {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (ε : ℝ) (_hε_pos : 0 < ε) (H : ℝ → ℝ → ℂ)
    (hH_cont : ContinuousOn (Function.uncurry H)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 6))
    (hH_0 : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      H 0 t = modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
    (hH_1 : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      H 1 t = _root_.circleMap w ε (t * Real.pi / 3))
    (hH_avoid : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6, H s t ≠ w)
    (hH_closed : ∀ s ∈ Set.Icc (0 : ℝ) 1, H s 0 = H s 6) :
    Complex.pathContourIntegral
      (fun t => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      0 6 (fun z => (z - w)⁻¹) =
    Complex.pathContourIntegral
      (fun t : ℝ => _root_.circleMap w ε (t * Real.pi / 3))
      0 6 (fun z => (z - w)⁻¹) := by
  -- The shifted homotopy u := H − w is jointly continuous and nonvanishing
  -- on the rectangle, so it admits a jointly continuous log lift.
  have h_u_cont : ContinuousOn (Function.uncurry (fun s t => H s t - w))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 6) := by
    have h_eq : Function.uncurry (fun s t => H s t - w) =
        fun p : ℝ × ℝ => Function.uncurry H p - w := rfl
    rw [h_eq]
    exact hH_cont.sub continuousOn_const
  obtain ⟨L, hL_cont, hL_exp₀⟩ :=
    continuous_log_lift_param_of_continuous_ne_zero
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 6)
      (fun s t => H s t - w) h_u_cont
      (fun s hs t ht => sub_ne_zero.mpr (hH_avoid s hs t ht))
  have hL_exp : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L s t) = H s t - w := hL_exp₀
  -- Membership facts used throughout.
  have h0_mem6 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 6 := by norm_num
  have h6_mem6 : (6 : ℝ) ∈ Set.Icc (0 : ℝ) 6 := by norm_num
  have h0_mem1 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1_mem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  -- The cross-section boundary difference τ s := L s 6 − L s 0 is continuous
  -- and lies in 2πi·ℤ for every s ∈ [0, 1] (closedness of H s).
  have h_τ_cont : Continuous (fun s => L s 6 - L s 0) := by
    have h6 : Continuous (fun s => L s 6) :=
      hL_cont.comp (continuous_id.prodMk continuous_const)
    have h0 : Continuous (fun s => L s 0) :=
      hL_cont.comp (continuous_id.prodMk continuous_const)
    exact h6.sub h0
  have h_τ_int : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ n : ℤ, L s 6 - L s 0 = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    intro s hs
    have h_exp_eq : Complex.exp (L s 6 - L s 0) = 1 := by
      rw [Complex.exp_sub, hL_exp s hs 6 h6_mem6, hL_exp s hs 0 h0_mem6,
        ← hH_closed s hs]
      exact div_self (sub_ne_zero.mpr (hH_avoid s hs 0 h0_mem6))
    exact Complex.exp_eq_one_iff.mp h_exp_eq
  -- Integer continuity: τ 0 = τ 1.
  have h_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hψ_int : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ n : ℤ, (L s 6 - L s 0).im / (2 * Real.pi) = (n : ℝ) := by
    intro s hs
    obtain ⟨n, hn⟩ := h_τ_int s hs
    refine ⟨n, ?_⟩
    have h_im : (L s 6 - L s 0).im = (n : ℝ) * (2 * Real.pi) := by
      rw [hn]
      simp [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    rw [h_im]
    field_simp
  have hψ_re : ∀ s ∈ Set.Icc (0 : ℝ) 1, (L s 6 - L s 0).re = 0 := by
    intro s hs
    obtain ⟨n, hn⟩ := h_τ_int s hs
    rw [hn]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  have h_τ_eq : L 0 6 - L 0 0 = L 1 6 - L 1 0 := by
    have hψ_cont : Continuous (fun s => (L s 6 - L s 0).im / (2 * Real.pi)) :=
      (Complex.continuous_im.comp h_τ_cont).div_const _
    obtain ⟨n₀, hn₀⟩ := hψ_int 0 h0_mem1
    obtain ⟨n₁, hn₁⟩ := hψ_int 1 h1_mem1
    have h_n_eq : n₀ = n₁ := by
      by_contra h_ne
      rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
      · -- n₀ < n₁: hit the half-integer n₀ + 1/2 by IVT.
        have h_le : (n₀ : ℝ) + 1 ≤ n₁ := by exact_mod_cast h_lt
        have h_mem : ((n₀ : ℝ) + 1 / 2) ∈ Set.Icc
            ((L (0 : ℝ) 6 - L 0 0).im / (2 * Real.pi))
            ((L (1 : ℝ) 6 - L 1 0).im / (2 * Real.pi)) := by
          rw [hn₀, hn₁]
          constructor <;> linarith
        obtain ⟨s, hs_mem, hs_val⟩ :=
          intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
            hψ_cont.continuousOn h_mem
        have hs_val' : (L s 6 - L s 0).im / (2 * Real.pi) = (n₀ : ℝ) + 1 / 2 := hs_val
        obtain ⟨m, hm⟩ := hψ_int s hs_mem
        have h_m_val : (m : ℝ) = (n₀ : ℝ) + 1 / 2 := by rw [← hm]; exact hs_val'
        have h_cast : ((2 * m : ℤ) : ℝ) = ((2 * n₀ + 1 : ℤ) : ℝ) := by
          push_cast; linarith
        have h2m : (2 * m : ℤ) = 2 * n₀ + 1 := by exact_mod_cast h_cast
        omega
      · -- n₁ < n₀: symmetric, with the decreasing-form IVT.
        have h_le : (n₁ : ℝ) + 1 ≤ n₀ := by exact_mod_cast h_gt
        have h_mem : ((n₁ : ℝ) + 1 / 2) ∈ Set.Icc
            ((L (1 : ℝ) 6 - L 1 0).im / (2 * Real.pi))
            ((L (0 : ℝ) 6 - L 0 0).im / (2 * Real.pi)) := by
          rw [hn₀, hn₁]
          constructor <;> linarith
        obtain ⟨s, hs_mem, hs_val⟩ :=
          intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
            hψ_cont.continuousOn h_mem
        have hs_val' : (L s 6 - L s 0).im / (2 * Real.pi) = (n₁ : ℝ) + 1 / 2 := hs_val
        obtain ⟨m, hm⟩ := hψ_int s hs_mem
        have h_m_val : (m : ℝ) = (n₁ : ℝ) + 1 / 2 := by rw [← hm]; exact hs_val'
        have h_cast : ((2 * m : ℤ) : ℝ) = ((2 * n₁ + 1 : ℤ) : ℝ) := by
          push_cast; linarith
        have h2m : (2 * m : ℤ) = 2 * n₁ + 1 := by exact_mod_cast h_cast
        omega
    -- Equal imaginary parts and zero real parts force τ 0 = τ 1.
    have h_im0 : (L (0 : ℝ) 6 - L 0 0).im = (n₀ : ℝ) * (2 * Real.pi) := by
      have h := hn₀
      field_simp at h
      linarith
    have h_im1 : (L (1 : ℝ) 6 - L 1 0).im = (n₁ : ℝ) * (2 * Real.pi) := by
      have h := hn₁
      field_simp at h
      linarith
    refine Complex.ext ?_ ?_
    · rw [hψ_re 0 h0_mem1, hψ_re 1 h1_mem1]
    · rw [h_im0, h_im1, h_n_eq]
  -- Left FTC bridge: the image-curve integral equals τ 0.
  have h_γ_ne : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w ≠ 0 := by
    intro t ht
    rw [← hH_0 t ht]
    exact sub_ne_zero.mpr (hH_avoid 0 h0_mem1 t ht)
  have h_L0_cont : Continuous (fun t => L 0 t) :=
    hL_cont.comp (continuous_const.prodMk continuous_id)
  have h_L0_exp : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L 0 t) =
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w := by
    intro t ht
    rw [hL_exp 0 h0_mem1 t ht, hH_0 t ht]
  have h_left := pathContourIntegral_inv_eq_log_lift_diff_F_Y_image_curve
    hδ hδY hR₀_pos hR₀_lt h_γ_ne (fun t => L 0 t) h_L0_cont h_L0_exp
  -- Right FTC bridge: the circle integral equals τ 1.
  have h_circle_C1 : ContDiff ℝ 1
      (fun t : ℝ => _root_.circleMap w ε (t * Real.pi / 3)) :=
    (contDiff_circleMap w ε).comp (by fun_prop)
  have h_circle_ne : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      _root_.circleMap w ε (t * Real.pi / 3) ≠ w := by
    intro t ht
    rw [← hH_1 t ht]
    exact hH_avoid 1 h1_mem1 t ht
  have h_L1_cont : Continuous (fun t => L 1 t) :=
    hL_cont.comp (continuous_const.prodMk continuous_id)
  have h_L1_exp : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L 1 t) = _root_.circleMap w ε (t * Real.pi / 3) - w := by
    intro t ht
    rw [hL_exp 1 h1_mem1 t ht, hH_1 t ht]
  have h_right := pathContourIntegral_inv_eq_log_lift_diff_of_contDiff
    (by norm_num : (0 : ℝ) ≤ 6)
    (fun t : ℝ => _root_.circleMap w ε (t * Real.pi / 3))
    h_circle_C1 h_circle_ne (fun t => L 1 t) h_L1_cont h_L1_exp
  -- Chain the three identities.
  rw [h_left, h_right]
  exact h_τ_eq

end NoWanderingDomains
