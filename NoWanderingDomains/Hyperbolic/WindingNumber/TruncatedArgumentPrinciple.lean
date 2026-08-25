/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.WindingNumber.LuneHalfAnnulus

/-! # The argument principle on the truncated region

The argument principle on the truncated region `F_Y = (Icc a b ×ℂ Icc e.im d) \\ ball e R₀`:
for `g` analytic on a neighborhood of `F_Y` and non-vanishing on the five boundary
pieces, the `(2πi)⁻¹`-normalized boundary integral of `g′/g` equals the divisor sum of
`g` on `F_Y` — the total zero count with multiplicity — with an existential
natural-number corollary. Companion bounds on the zero count: at least one if `g`
vanishes somewhere in the region, at most one for a unique simple zero, and at least
two for either two distinct zeros or a double zero.
-/

namespace Complex
open MeasureTheory

set_option maxHeartbeats 400000 in
-- The proof clones the Weierstrass-factorization structure of
-- `cIntegralLogDeriv_isNat_of_nonzero_on_rectBoundary` over the F_Y
-- region (closed rectangle minus open upper half-disk on the bottom
-- edge), applying `rectBoundary` and the upper-semicircle integral to
-- the rational factor `r` and the F_Y-shape Cauchy-Goursat
-- (`integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn`) to
-- the analytic non-vanishing factor `h`. The combined elaboration
-- pressure (codiscrete + AccPt + 5 edge-membership +
-- arc-membership + divisor-support strict-interior analysis) exceeds
-- the default heartbeat limit.
/-- **Argument principle on a rectangle with an upper half-disk removed
from the bottom boundary.** For a function `g` analytic on a neighborhood
of the closed region `F_Y := (Icc a b ×ℂ Icc e.im d) \ ball e R₀` — the
rectangle `[a, b] × [e.im, d]` with the open upper half of the disk
centered at `e` on the bottom edge removed — and non-vanishing on each
of the five boundary pieces (the four rectangle edges and the upper
semicircle `|z − e| = R₀, Im z ≥ e.im`), the contour integral around
`∂F_Y` (CCW with the region interior on the left) of `g'/g` is `2πi`
times the count of zeros of `g` inside `F_Y^o`.

This is the **truncated `Γ(2)` fundamental domain argument principle**:
with `a = 0`, `b = 1`, `e.im = 0`, `e = 1/2`, `R₀ = 1/2`, `d = Y`, the
region `F_Y` is the truncation of the half-fundamental-domain
`F = {0 ≤ Re τ ≤ 1, 1 ≤ |2τ − 1|, Im τ > 0}` to `Im τ ≤ Y`. Applying
this theorem to `g(τ) := λ(τ) − w` (analytic on `ℍ ⊃ F_Y`,
non-vanishing on `∂F_Y` for `Im w > 0` by the boundary-image analysis
of `λ`) counts preimages of `w` under `λ` inside `F^o`.

The proof clones the Weierstrass-factorization structure of
`cIntegralLogDeriv_isNat_of_nonzero_on_rectBoundary`: factor
`g = (∏ᶠ u, (· − u)^{n_u}) · h` (with `n_u` the multiplicities of
zeros of `g` in `F_Y^o` and `h` analytic + non-vanishing on a
neighborhood of `F_Y`), split the log-derivative as
`g'/g = r'/r + h'/h`, integrate `h'/h` around `∂F_Y` via
`integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn` (giving
zero), and reduce the `r'/r` integral to a Finset sum of single-zero
contributions, each evaluated via the rectangle and upper-semicircle
winding numbers. -/
theorem cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk
    (g : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hab : a < b) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    (hg_bot_left : ∀ x ∈ Set.Icc a (e.re - R₀),
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (e.re + R₀) b,
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc a b, g ((x : ℂ) + (d : ℂ) * Complex.I) ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc e.im d, g ((b : ℂ) + (y : ℂ) * Complex.I) ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc e.im d, g ((a : ℂ) + (y : ℂ) * Complex.I) ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      g (_root_.circleMap e R₀ θ) ≠ 0) :
    (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in a..(e.re - R₀), deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        g ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
      (∫ x in (e.re + R₀)..b, deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        g ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
      Complex.I * (∫ y in e.im..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
        g ((b : ℂ) + (y : ℂ) * Complex.I)) -
      (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
        g ((x : ℂ) + (d : ℂ) * Complex.I)) -
      Complex.I * (∫ y in e.im..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
        g ((a : ℂ) + (y : ℂ) * Complex.I)) -
      (∫ θ in (0 : ℝ)..Real.pi, deriv g (_root_.circleMap e R₀ θ) /
        g (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) =
    ((∑ᶠ u, MeromorphicOn.divisor g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) u).toNat : ℂ) := by
  -- Closed F_Y region.
  set F : Set ℂ := (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ with hF_def
  have hg_mer : MeromorphicOn g F := hg.meromorphicOn
  have h_e_im_lt_d : e.im < d := by linarith
  have hF_pathConnected : IsPathConnected F :=
    isPathConnected_rectMinusUpperHalfDisk a b d e R₀ hR₀ hab h_a_lt h_lt_b h_e_im_R0_lt_d
  have hF_preconn : IsPreconnected F := hF_pathConnected.isConnected.isPreconnected
  -- Witness corner z₀ = (a, e.im).
  set z₀ : ℂ := (a : ℂ) + (e.im : ℂ) * Complex.I with hz₀_def
  have hz₀_re : z₀.re = a := by
    simp [hz₀_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hz₀_im : z₀.im = e.im := by
    simp [hz₀_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hz₀_in_F : z₀ ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hz₀_re, Set.mem_Icc]; exact ⟨le_refl _, hab.le⟩
      · rw [hz₀_im, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (z₀ - e).re = a - e.re := by
        rw [Complex.sub_re, hz₀_re]
      have h_abs := Complex.abs_re_le_norm (z₀ - e)
      rw [h_re_diff, abs_of_neg (by linarith : a - e.re < 0)] at h_abs
      linarith
  have hz₀_g_ne : g z₀ ≠ 0 :=
    hg_bot_left a (Set.left_mem_Icc.mpr (by linarith))
  have hz₀_analytic : AnalyticAt ℂ g z₀ := hg z₀ hz₀_in_F
  have hz₀_order_ne_top : meromorphicOrderAt g z₀ ≠ ⊤ := by
    rw [hz₀_analytic.meromorphicOrderAt_eq]
    intro h
    rw [ENat.map_eq_top_iff] at h
    have h0 : analyticOrderAt g z₀ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hz₀_g_ne)
    rw [h0] at h
    exact ENat.zero_ne_top h
  have hg_order : ∀ u ∈ F, meromorphicOrderAt g u ≠ ⊤ := by
    intro u hu
    exact hg_mer.meromorphicOrderAt_ne_top_of_isPreconnected hF_preconn
      hz₀_in_F hu hz₀_order_ne_top
  have hF_compact : IsCompact F :=
    (IsCompact.reProdIm isCompact_Icc isCompact_Icc).diff Metric.isOpen_ball
  have hdiv_finite : (MeromorphicOn.divisor g F).support.Finite :=
    Function.locallyFinsuppWithin.finiteSupport _ hF_compact
  obtain ⟨h, h_analytic, h_nonzero, h_factor⟩ :=
    hg_mer.extract_zeros_poles
      (fun u : F => hg_order u.1 u.2)
      hdiv_finite
  have hD_nonneg : 0 ≤ MeromorphicOn.divisor g F :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg
  set r : ℂ → ℂ :=
    ∏ᶠ u, (· - u) ^ ((MeromorphicOn.divisor g F) u) with hr_def
  have hr_analytic : ∀ z, AnalyticAt ℂ r z := fun z =>
    Function.FactorizedRational.analyticAt (hD_nonneg z)
  have hF_ntriv : F.Nontrivial := by
    refine ⟨z₀, hz₀_in_F, (b : ℂ) + (d : ℂ) * Complex.I, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [Complex.mem_reProdIm]
        refine ⟨?_, ?_⟩
        · show _ ∈ Set.Icc a b
          have h_eq : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by
            simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
          rw [h_eq]; exact Set.right_mem_Icc.mpr hab.le
        · show _ ∈ Set.Icc e.im d
          have h_eq : ((b : ℂ) + (d : ℂ) * Complex.I).im = d := by
            simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
          rw [h_eq]; exact Set.right_mem_Icc.mpr (by linarith)
      · rw [Metric.mem_ball, Complex.dist_eq]; push Not
        have h_re_diff : (((b : ℂ) + (d : ℂ) * Complex.I) - e).re = b - e.re := by
          simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have h_abs := Complex.abs_re_le_norm
          (((b : ℂ) + (d : ℂ) * Complex.I) - e)
        rw [h_re_diff, abs_of_pos (by linarith : 0 < b - e.re)] at h_abs
        linarith
    · intro h_eq
      have h_re : z₀.re = ((b : ℂ) + (d : ℂ) * Complex.I).re := by rw [h_eq]
      rw [hz₀_re] at h_re
      have : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this] at h_re
      linarith
  have h_accpt : ∀ z ∈ F, AccPt z (Filter.principal F) :=
    fun z hz => hF_preconn.preperfect_of_nontrivial hF_ntriv z hz
  have h_factor_mul : g =ᶠ[Filter.codiscreteWithin F] (fun w => r w * h w) := by
    filter_upwards [h_factor] with w hw
    simpa [smul_eq_mul] using hw
  have h_nhds_eq : ∀ z ∈ F, g =ᶠ[nhds z] (fun w => r w * h w) := by
    intro z hz
    have hz_g_an : AnalyticAt ℂ g z := hg z hz
    have hz_r_an : AnalyticAt ℂ r z := hr_analytic z
    have hz_h_an : AnalyticAt ℂ h z := h_analytic z hz
    have hz_rh_an : AnalyticAt ℂ (fun w => r w * h w) z := hz_r_an.mul hz_h_an
    have h_pnctd := hz_g_an.meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      hz_rh_an.meromorphicAt hz (h_accpt z hz) h_factor_mul
    exact (AnalyticAt.frequently_eq_iff_eventually_eq hz_g_an hz_rh_an).mp h_pnctd.frequently
  have h_g_eq : ∀ z ∈ F, g z = r z * h z := fun z hz =>
    (h_nhds_eq z hz).eq_of_nhds
  have h_deriv_eq : ∀ z ∈ F, deriv g z = deriv (fun w => r w * h w) z := fun z hz =>
    (h_nhds_eq z hz).deriv_eq
  have h_div_zero_at_edge : ∀ z ∈ F, g z ≠ 0 →
      (MeromorphicOn.divisor g F) z = 0 := by
    intro z hz hz_g_ne
    rw [MeromorphicOn.divisor_apply hg_mer hz,
        (hg z hz).meromorphicOrderAt_eq,
        analyticOrderAt_eq_zero.mpr (Or.inr hz_g_ne)]
    simp
  have hr_ne_at_edge : ∀ z ∈ F, g z ≠ 0 → r z ≠ 0 := fun z hz hz_g_ne =>
    Function.FactorizedRational.ne_zero (h_div_zero_at_edge z hz hz_g_ne)
  -- Boundary membership (5 edges + arc) in F.
  have h_bot_left_mem : ∀ x ∈ Set.Icc a (e.re - R₀),
      ((x : ℂ) + (e.im : ℂ) * Complex.I) ∈ F := by
    intro x hx
    rw [Set.mem_Icc] at hx
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show _ ∈ Set.Icc a b
        have h_re_eq : ((x : ℂ) + (e.im : ℂ) * Complex.I).re = x := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_re_eq, Set.mem_Icc]; exact ⟨hx.1, by linarith [hx.2]⟩
      · show _ ∈ Set.Icc e.im d
        have h_im_eq : ((x : ℂ) + (e.im : ℂ) * Complex.I).im = e.im := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_im_eq, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (((x : ℂ) + (e.im : ℂ) * Complex.I) - e).re = x - e.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have h_abs := Complex.abs_re_le_norm
        (((x : ℂ) + (e.im : ℂ) * Complex.I) - e)
      rw [h_re_diff, abs_of_nonpos (by linarith [hx.2] : x - e.re ≤ 0)] at h_abs
      linarith
  have h_bot_right_mem : ∀ x ∈ Set.Icc (e.re + R₀) b,
      ((x : ℂ) + (e.im : ℂ) * Complex.I) ∈ F := by
    intro x hx
    rw [Set.mem_Icc] at hx
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show _ ∈ Set.Icc a b
        have h_re_eq : ((x : ℂ) + (e.im : ℂ) * Complex.I).re = x := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_re_eq, Set.mem_Icc]; exact ⟨by linarith [hx.1], hx.2⟩
      · show _ ∈ Set.Icc e.im d
        have h_im_eq : ((x : ℂ) + (e.im : ℂ) * Complex.I).im = e.im := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_im_eq, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (((x : ℂ) + (e.im : ℂ) * Complex.I) - e).re = x - e.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have h_abs := Complex.abs_re_le_norm
        (((x : ℂ) + (e.im : ℂ) * Complex.I) - e)
      rw [h_re_diff, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - e.re)] at h_abs
      linarith
  have h_top_mem : ∀ x ∈ Set.Icc a b,
      ((x : ℂ) + (d : ℂ) * Complex.I) ∈ F := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show _ ∈ Set.Icc a b
        have h_re_eq : ((x : ℂ) + (d : ℂ) * Complex.I).re = x := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_re_eq]; exact hx
      · show _ ∈ Set.Icc e.im d
        have h_im_eq : ((x : ℂ) + (d : ℂ) * Complex.I).im = d := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_im_eq, Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_im_diff : (((x : ℂ) + (d : ℂ) * Complex.I) - e).im = d - e.im := by
        simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have h_abs := Complex.abs_im_le_norm
        (((x : ℂ) + (d : ℂ) * Complex.I) - e)
      rw [h_im_diff, abs_of_pos (by linarith : (0:ℝ) < d - e.im)] at h_abs
      linarith
  have h_right_mem : ∀ y ∈ Set.Icc e.im d,
      ((b : ℂ) + (y : ℂ) * Complex.I) ∈ F := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show _ ∈ Set.Icc a b
        have h_re_eq : ((b : ℂ) + (y : ℂ) * Complex.I).re = b := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_re_eq, Set.mem_Icc]; exact ⟨hab.le, le_refl _⟩
      · show _ ∈ Set.Icc e.im d
        have h_im_eq : ((b : ℂ) + (y : ℂ) * Complex.I).im = y := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_im_eq]; exact hy
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (((b : ℂ) + (y : ℂ) * Complex.I) - e).re = b - e.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have h_abs := Complex.abs_re_le_norm
        (((b : ℂ) + (y : ℂ) * Complex.I) - e)
      rw [h_re_diff, abs_of_pos (by linarith : 0 < b - e.re)] at h_abs
      linarith
  have h_left_mem : ∀ y ∈ Set.Icc e.im d,
      ((a : ℂ) + (y : ℂ) * Complex.I) ∈ F := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show _ ∈ Set.Icc a b
        have h_re_eq : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_re_eq, Set.mem_Icc]; exact ⟨le_refl _, hab.le⟩
      · show _ ∈ Set.Icc e.im d
        have h_im_eq : ((a : ℂ) + (y : ℂ) * Complex.I).im = y := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_im_eq]; exact hy
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (((a : ℂ) + (y : ℂ) * Complex.I) - e).re = a - e.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have h_abs := Complex.abs_re_le_norm
        (((a : ℂ) + (y : ℂ) * Complex.I) - e)
      rw [h_re_diff, abs_of_neg (by linarith : a - e.re < 0)] at h_abs
      linarith
  have h_arc_mem : ∀ θ ∈ Set.Icc (0:ℝ) Real.pi,
      _root_.circleMap e R₀ θ ∈ F := by
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show _ ∈ Set.Icc a b
        rw [_root_.circleMap]
        have h_re_eq : (e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re =
            e.re + R₀ * Real.cos θ := by
          rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
          ring
        rw [h_re_eq, Set.mem_Icc]
        have h_cos := Real.cos_le_one θ
        have h_cos_ge := Real.neg_one_le_cos θ
        exact ⟨by nlinarith [hR₀], by nlinarith [hR₀]⟩
      · show _ ∈ Set.Icc e.im d
        rw [_root_.circleMap]
        have h_im_eq : (e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im =
            e.im + R₀ * Real.sin θ := by
          rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
          ring
        rw [h_im_eq, Set.mem_Icc]
        have h_sin_nn := Real.sin_nonneg_of_mem_Icc (Set.mem_Icc.mpr hθ)
        have h_sin_le_one := Real.sin_le_one θ
        exact ⟨by nlinarith [hR₀], by nlinarith [hR₀]⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      rw [_root_.circleMap]
      have h_norm_eq : ‖e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - e‖ = R₀ := by
        rw [show e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - e =
            (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) from by ring,
          norm_mul, Complex.norm_real,
          Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg hR₀.le]
      rw [h_norm_eq]
  -- g'/g = r'/r + h'/h on boundary points where g ≠ 0.
  have h_logDeriv_split : ∀ z ∈ F, g z ≠ 0 →
      deriv (fun w => r w * h w) z / (r z * h z) =
      deriv r z / r z + deriv h z / h z := by
    intro z hz hz_g_ne
    have hr_ne := hr_ne_at_edge z hz hz_g_ne
    have hh_ne : h z ≠ 0 := h_nonzero ⟨z, hz⟩
    have hr_diff : DifferentiableAt ℂ r z := (hr_analytic z).differentiableAt
    have hh_diff : DifferentiableAt ℂ h z := (h_analytic z hz).differentiableAt
    have := logDeriv_mul z hr_ne hh_ne hr_diff hh_diff
    simp only [logDeriv_apply] at this
    exact this
  have h_int_eq_at_edge : ∀ z ∈ F, g z ≠ 0 →
      deriv g z / g z = deriv r z / r z + deriv h z / h z := by
    intro z hz hz_g_ne
    rw [h_g_eq z hz, h_deriv_eq z hz]
    exact h_logDeriv_split z hz hz_g_ne
  -- Per-edge/arc integrand equality.
  have h_int_bot_left : (∫ x in a..(e.re - R₀), deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
      g ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
      (∫ x in a..(e.re - R₀), deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx_Icc : x ∈ Set.Icc a (e.re - R₀) := by
      rw [Set.uIcc_of_le (by linarith : a ≤ e.re - R₀)] at hx; exact hx
    exact h_int_eq_at_edge _ (h_bot_left_mem x hx_Icc) (hg_bot_left x hx_Icc)
  have h_int_bot_right :
      (∫ x in (e.re + R₀)..b, deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        g ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
      (∫ x in (e.re + R₀)..b, deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx_Icc : x ∈ Set.Icc (e.re + R₀) b := by
      rw [Set.uIcc_of_le (by linarith : e.re + R₀ ≤ b)] at hx; exact hx
    exact h_int_eq_at_edge _ (h_bot_right_mem x hx_Icc) (hg_bot_right x hx_Icc)
  have h_int_top : (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
      g ((x : ℂ) + (d : ℂ) * Complex.I)) =
      (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx_Icc : x ∈ Set.Icc a b := by
      rw [Set.uIcc_of_le hab.le] at hx; exact hx
    exact h_int_eq_at_edge _ (h_top_mem x hx_Icc) (hg_top x hx_Icc)
  have h_int_right : (∫ y in e.im..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
      g ((b : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in e.im..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy_Icc : y ∈ Set.Icc e.im d := by
      rw [Set.uIcc_of_le h_e_im_lt_d.le] at hy; exact hy
    exact h_int_eq_at_edge _ (h_right_mem y hy_Icc) (hg_right y hy_Icc)
  have h_int_left : (∫ y in e.im..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
      g ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in e.im..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy_Icc : y ∈ Set.Icc e.im d := by
      rw [Set.uIcc_of_le h_e_im_lt_d.le] at hy; exact hy
    exact h_int_eq_at_edge _ (h_left_mem y hy_Icc) (hg_left y hy_Icc)
  have h_int_arc : (∫ θ in (0:ℝ)..Real.pi, deriv g (_root_.circleMap e R₀ θ) /
      g (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      (∫ θ in (0:ℝ)..Real.pi,
        (deriv r (_root_.circleMap e R₀ θ) /
          r (_root_.circleMap e R₀ θ) +
          deriv h (_root_.circleMap e R₀ θ) /
          h (_root_.circleMap e R₀ θ)) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ_Icc : θ ∈ Set.Icc (0:ℝ) Real.pi := by
      rw [Set.uIcc_of_le Real.pi_nonneg] at hθ; exact hθ
    have h_eq := h_int_eq_at_edge _ (h_arc_mem θ hθ_Icc) (hg_arc θ hθ_Icc)
    change deriv g (_root_.circleMap e R₀ θ) / g (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ)) =
      (deriv r (_root_.circleMap e R₀ θ) / r (_root_.circleMap e R₀ θ) +
        deriv h (_root_.circleMap e R₀ θ) / h (_root_.circleMap e R₀ θ)) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))
    rw [h_eq]
  -- h analytic & nonzero on F → h'/h is DifferentiableOn F.
  have h_h_ne : ∀ z ∈ F, h z ≠ 0 := fun z hz => h_nonzero ⟨z, hz⟩
  have h_dh_div_h_diff : DifferentiableOn ℂ (fun z => deriv h z / h z) F := by
    intro z hz
    have hh_ne := h_h_ne z hz
    have h_dh_an : AnalyticAt ℂ (deriv h) z := (h_analytic z hz).deriv
    have h_h_an : AnalyticAt ℂ h z := h_analytic z hz
    exact (h_dh_an.div h_h_an hh_ne).differentiableAt.differentiableWithinAt
  -- For each z ∈ F, AnalyticAt h z + h z ≠ 0 give an open nhd of z where h is analytic & ≠ 0.
  have h_an_and_ne_open : IsOpen ({z : ℂ | AnalyticAt ℂ h z} ∩ {z : ℂ | h z ≠ 0}) := by
    rw [isOpen_iff_eventually]
    rintro z ⟨hz_an, hz_ne⟩
    have h_an_ev : ∀ᶠ w in nhds z, AnalyticAt ℂ h w := hz_an.eventually_analyticAt
    have h_ne_ev : ∀ᶠ w in nhds z, h w ≠ 0 :=
      hz_an.continuousAt.eventually_ne hz_ne
    filter_upwards [h_an_ev, h_ne_ev] with w hw_an hw_ne
    exact ⟨hw_an, hw_ne⟩
  have h_F_sub_an_ne : F ⊆ {z : ℂ | AnalyticAt ℂ h z} ∩ {z : ℂ | h z ≠ 0} :=
    fun z hz => ⟨h_analytic z hz, h_h_ne z hz⟩
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    hF_compact.exists_thickening_subset_open h_an_and_ne_open h_F_sub_an_ne
  -- Reduce δ to be ≤ R₀ for use in R₀'.
  set δ' : ℝ := min δ R₀ with hδ'_def
  have hδ'_pos : 0 < δ' := lt_min hδ_pos hR₀
  have hδ'_le_δ : δ' ≤ δ := min_le_left _ _
  have hδ'_le_R₀ : δ' ≤ R₀ := min_le_right _ _
  -- Define R₀' := R₀ - δ'/2.
  set R₀' : ℝ := R₀ - δ' / 2 with hR₀'_def
  have hR₀'_pos : 0 < R₀' := by
    rw [hR₀'_def]; linarith [hδ'_le_R₀, hδ'_pos]
  have hR₀'_lt : R₀' < R₀ := by rw [hR₀'_def]; linarith [hδ'_pos]
  -- Sub : (Ioo a b ×ℂ Ioo e.im d) \ closedBall e R₀' ⊆ thickening δ F.
  have h_sub_thickening :
      ((Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀') ⊆
        Metric.thickening δ F := by
    rintro z ⟨hz_box, hz_not_closedR₀'⟩
    rw [Complex.mem_reProdIm] at hz_box
    obtain ⟨hz_re_Ioo, hz_im_Ioo⟩ := hz_box
    rw [Set.mem_Ioo] at hz_re_Ioo hz_im_Ioo
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz_not_closedR₀'
    push Not at hz_not_closedR₀'
    have hz_dist_gt : R₀' < ‖z - e‖ := hz_not_closedR₀'
    rw [Metric.mem_thickening_iff]
    by_cases hz_in_F : ‖z - e‖ ≥ R₀
    · -- z ∈ F (or close).
      refine ⟨z, ⟨?_, ?_⟩, by rw [dist_self]; exact hδ_pos⟩
      · rw [Complex.mem_reProdIm]
        refine ⟨Set.Ioo_subset_Icc_self hz_re_Ioo |> Set.mem_Icc.mpr ∘ id, ?_⟩
        · exact Set.Ioo_subset_Icc_self hz_im_Ioo
      · rw [Metric.mem_ball, Complex.dist_eq]; push Not; exact hz_in_F
    · -- z in annulus: R₀' < ‖z - e‖ < R₀.
      push Not at hz_in_F
      have h_z_norm_pos : 0 < ‖z - e‖ := by linarith [hR₀'_pos]
      have h_z_norm_ne : ‖z - e‖ ≠ 0 := ne_of_gt h_z_norm_pos
      -- Project radially outward: z' := e + (R₀/‖z - e‖) · (z - e).
      set z' : ℂ := e + ((R₀ / ‖z - e‖ : ℝ) : ℂ) * (z - e) with hz'_def
      have hz'_sub : z' - e = ((R₀ / ‖z - e‖ : ℝ) : ℂ) * (z - e) := by
        rw [hz'_def]; ring
      have h_R₀_div_pos : 0 < R₀ / ‖z - e‖ := div_pos hR₀ h_z_norm_pos
      have h_R₀_div_ge_one : 1 ≤ R₀ / ‖z - e‖ := by
        rw [le_div_iff₀ h_z_norm_pos]; linarith
      have hz'_norm : ‖z' - e‖ = R₀ := by
        rw [hz'_sub, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg h_R₀_div_pos.le, div_mul_cancel₀ _ h_z_norm_ne]
      -- z' is in F.
      have hz'_re_diff : (z' - e).re = (R₀ / ‖z - e‖) * (z - e).re := by
        rw [hz'_sub]
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      have hz'_im_diff : (z' - e).im = (R₀ / ‖z - e‖) * (z - e).im := by
        rw [hz'_sub]
        simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      have hz'_re : z'.re = e.re + (R₀ / ‖z - e‖) * (z.re - e.re) := by
        have h1 : z'.re = e.re + (z' - e).re := by simp [Complex.sub_re]
        rw [h1, hz'_re_diff, Complex.sub_re]
      have hz'_im : z'.im = e.im + (R₀ / ‖z - e‖) * (z.im - e.im) := by
        have h1 : z'.im = e.im + (z' - e).im := by simp [Complex.sub_im]
        rw [h1, hz'_im_diff, Complex.sub_im]
      -- |z'.re - e.re| ≤ R₀ and z'.im - e.im ≥ 0 with ≤ R₀.
      have h_z'_re_abs : |z'.re - e.re| ≤ R₀ := by
        have h_re_eq : z'.re - e.re = (R₀ / ‖z - e‖) * (z.re - e.re) := by
          rw [hz'_re]; ring
        have h_abs_le := Complex.abs_re_le_norm (z' - e)
        rw [show (z' - e).re = z'.re - e.re from by simp [Complex.sub_re], h_re_eq,
            hz'_norm] at h_abs_le
        rw [h_re_eq]; exact h_abs_le
      have h_z'_im_abs : |z'.im - e.im| ≤ R₀ := by
        have h_im_eq : z'.im - e.im = (R₀ / ‖z - e‖) * (z.im - e.im) := by
          rw [hz'_im]; ring
        have h_abs_le := Complex.abs_im_le_norm (z' - e)
        rw [show (z' - e).im = z'.im - e.im from by simp [Complex.sub_im], h_im_eq,
            hz'_norm] at h_abs_le
        rw [h_im_eq]; exact h_abs_le
      have h_z'_im_nn : 0 ≤ z'.im - e.im := by
        have h_im_eq : z'.im - e.im = (R₀ / ‖z - e‖) * (z.im - e.im) := by
          rw [hz'_im]; ring
        have h_z_im_nn : 0 ≤ z.im - e.im := by linarith [hz_im_Ioo.1]
        rw [h_im_eq]; exact mul_nonneg h_R₀_div_pos.le h_z_im_nn
      have hz'_in_F : z' ∈ F := by
        refine ⟨?_, ?_⟩
        · rw [Complex.mem_reProdIm]
          refine ⟨?_, ?_⟩
          · rw [Set.mem_Icc]
            refine ⟨?_, ?_⟩
            · have h_le := abs_le.mp h_z'_re_abs
              linarith [h_le.1, h_a_lt]
            · have h_le := abs_le.mp h_z'_re_abs
              linarith [h_le.2, h_lt_b]
          · rw [Set.mem_Icc]
            refine ⟨by linarith [h_z'_im_nn], ?_⟩
            have h_le := abs_le.mp h_z'_im_abs
            linarith [h_le.2, h_e_im_R0_lt_d]
        · rw [Metric.mem_ball, Complex.dist_eq, hz'_norm]
          exact lt_irrefl R₀
      -- ‖z - z'‖ < δ/2 ≤ δ.
      have h_z_z'_sub : z - z' = ((1 - R₀ / ‖z - e‖ : ℝ) : ℂ) * (z - e) := by
        rw [hz'_def]; push_cast; ring
      have h_one_minus : 1 - R₀ / ‖z - e‖ ≤ 0 := by linarith
      have h_dist_z_z' : dist z z' = R₀ - ‖z - e‖ := by
        rw [dist_eq_norm, h_z_z'_sub, norm_mul, Complex.norm_real,
            Real.norm_eq_abs,
            abs_of_nonpos h_one_minus]
        rw [neg_sub, sub_mul, div_mul_cancel₀ _ h_z_norm_ne, one_mul]
      have h_dist_lt : dist z z' < δ := by
        rw [h_dist_z_z']
        have : R₀ - ‖z - e‖ < δ' / 2 := by linarith
        linarith [hδ'_le_δ]
      exact ⟨z', hz'_in_F, h_dist_lt⟩
  -- h'/h DifferentiableOn (Ioo a b ×ℂ Ioo e.im d) \ closedBall e R₀'.
  have h_dh_div_h_diff_enlarged : DifferentiableOn ℂ (fun z => deriv h z / h z)
      ((Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀') := by
    intro z hz
    have hz_in : z ∈ Metric.thickening δ F := h_sub_thickening hz
    have hz_in_an_ne := hδ_sub hz_in
    obtain ⟨hz_an, hz_ne⟩ := hz_in_an_ne
    have h_dh_an : AnalyticAt ℂ (deriv h) z := hz_an.deriv
    exact (h_dh_an.div hz_an hz_ne).differentiableAt.differentiableWithinAt
  -- Apply F_Y CG to h'/h.
  have h_h_cont_F : ContinuousOn (fun z => deriv h z / h z) F :=
    h_dh_div_h_diff.continuousOn
  have h_cauchy_h :=
    integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn
      (fun z => deriv h z / h z) a b d e R₀
      hab h_e_im_lt_d hR₀ h_a_lt h_lt_b h_e_im_R0_lt_d h_h_cont_F
      ⟨R₀', hR₀'_pos, hR₀'_lt, h_dh_div_h_diff_enlarged⟩
  -- Dsupp.
  set Dsupp := hdiv_finite.toFinset with hDsupp_def
  -- Strict interior characterization of Dsupp.
  have hsupp_in_open : ∀ u ∈ Dsupp,
      u ∈ (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro u hu
    have hu_supp : u ∈ (MeromorphicOn.divisor g F).support := by
      simpa [hDsupp_def] using hu
    have hu_F : u ∈ F :=
      (MeromorphicOn.divisor g F).supportWithinDomain hu_supp
    -- u not on any boundary piece.
    obtain ⟨hu_box, hu_not_ball⟩ := hu_F
    rw [Complex.mem_reProdIm] at hu_box
    obtain ⟨hu_re_Icc, hu_im_Icc⟩ := hu_box
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Ioo]
        refine ⟨lt_of_le_of_ne hu_re_Icc.1 (fun h_eq => ?_),
                lt_of_le_of_ne hu_re_Icc.2 (fun h_eq => ?_)⟩
        · -- u.re = a, then u is on left edge.
          have hu_eq : u = (a : ℂ) + (u.im : ℂ) * Complex.I := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im, ← h_eq]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
          rw [hu_eq] at hu_supp
          apply hu_supp
          exact h_div_zero_at_edge ((a : ℂ) + (u.im : ℂ) * Complex.I)
            (h_left_mem u.im hu_im_Icc) (hg_left u.im hu_im_Icc)
        · -- u.re = b, then u is on right edge.
          have hu_eq : u = (b : ℂ) + (u.im : ℂ) * Complex.I := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im, h_eq]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
          rw [hu_eq] at hu_supp
          apply hu_supp
          exact h_div_zero_at_edge ((b : ℂ) + (u.im : ℂ) * Complex.I)
            (h_right_mem u.im hu_im_Icc) (hg_right u.im hu_im_Icc)
      · rw [Set.mem_Ioo]
        refine ⟨lt_of_le_of_ne hu_im_Icc.1 (fun h_eq => ?_),
                lt_of_le_of_ne hu_im_Icc.2 (fun h_eq => ?_)⟩
        · -- u.im = e.im, then u is on bottom: split into bot_left, bot_middle (arc actually,
          -- but u ∉ ball means u not in middle), bot_right.
          have hu_eq : u = (u.re : ℂ) + (e.im : ℂ) * Complex.I := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im, ← h_eq]
          -- u.re ∈ [a, e.re - R₀] ∪ [e.re + R₀, b] because u ∉ ball.
          have h_u_re_outside : u.re ≤ e.re - R₀ ∨ e.re + R₀ ≤ u.re := by
            by_contra h
            push Not at h
            obtain ⟨h1, h2⟩ := h
            apply hu_not_ball
            rw [Metric.mem_ball, Complex.dist_eq]
            have h_uminus_im : (u - e).im = 0 := by
              rw [Complex.sub_im, ← h_eq]; ring
            have h_norm_eq_re : ‖u - e‖ = |(u - e).re| := by
              have h_sq : ‖u - e‖^2 = (u - e).re^2 := by
                rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, h_uminus_im]
                ring
              have h_nn : 0 ≤ ‖u - e‖ := norm_nonneg _
              have h_abs_nn : 0 ≤ |(u - e).re| := abs_nonneg _
              have h_abs_sq : |(u - e).re|^2 = (u - e).re^2 := sq_abs _
              have h_eq_sq : ‖u - e‖^2 = |(u - e).re|^2 := by rw [h_sq, h_abs_sq]
              nlinarith [sq_nonneg (‖u - e‖ - |(u - e).re|),
                sq_nonneg (‖u - e‖ + |(u - e).re|), h_eq_sq, h_nn, h_abs_nn]
            rw [h_norm_eq_re, Complex.sub_re, abs_lt]
            constructor <;> linarith
          rcases h_u_re_outside with h_left | h_right
          · rw [hu_eq] at hu_supp
            apply hu_supp
            exact h_div_zero_at_edge ((u.re : ℂ) + (e.im : ℂ) * Complex.I)
              (h_bot_left_mem u.re (Set.mem_Icc.mpr ⟨hu_re_Icc.1, h_left⟩))
              (hg_bot_left u.re (Set.mem_Icc.mpr ⟨hu_re_Icc.1, h_left⟩))
          · rw [hu_eq] at hu_supp
            apply hu_supp
            exact h_div_zero_at_edge ((u.re : ℂ) + (e.im : ℂ) * Complex.I)
              (h_bot_right_mem u.re (Set.mem_Icc.mpr ⟨h_right, hu_re_Icc.2⟩))
              (hg_bot_right u.re (Set.mem_Icc.mpr ⟨h_right, hu_re_Icc.2⟩))
        · -- u.im = d, then u is on top edge.
          have hu_eq : u = (u.re : ℂ) + (d : ℂ) * Complex.I := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im, h_eq]
          rw [hu_eq] at hu_supp
          apply hu_supp
          exact h_div_zero_at_edge ((u.re : ℂ) + (d : ℂ) * Complex.I)
            (h_top_mem u.re hu_re_Icc) (hg_top u.re hu_re_Icc)
    · -- u ∉ closedBall e R₀: u ∉ ball + u not on arc → strict outside.
      intro h_in_closed
      rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_closed
      -- u not on ball (open).
      have h_norm_lt_or_eq : ‖u - e‖ < R₀ ∨ ‖u - e‖ = R₀ :=
        lt_or_eq_of_le h_in_closed
      rcases h_norm_lt_or_eq with h_lt | h_eq
      · apply hu_not_ball
        rw [Metric.mem_ball, Complex.dist_eq]; exact h_lt
      · -- ‖u - e‖ = R₀: u on the circle |z - e| = R₀.
        -- u.im ≥ e.im (since u ∈ Icc e.im d and u ∉ middle bottom).
        -- Hence u = circleMap e R₀ θ for some θ ∈ [0, π]. Apply hg_arc.
        have hu_im_ge : e.im ≤ u.im := hu_im_Icc.1
        have h_uminus_im_nn : 0 ≤ (u - e).im := by
          rw [Complex.sub_im]; linarith
        -- u = e + R₀ * exp(I*θ) where θ = arg(u - e), which is in [0, π].
        have h_arg_in : (u - e).arg ∈ Set.Icc (0 : ℝ) Real.pi := by
          rw [Set.mem_Icc]
          have h_uminus_ne : u - e ≠ 0 := by
            intro h_z; rw [h_z, norm_zero] at h_eq; linarith
          refine ⟨?_, Complex.arg_le_pi (u - e)⟩
          exact Complex.arg_nonneg_iff.mpr h_uminus_im_nn
        have h_circle : _root_.circleMap e R₀ (u - e).arg = u := by
          rw [_root_.circleMap]
          have h_norm_mul := Complex.norm_mul_exp_arg_mul_I (u - e)
          rw [h_eq] at h_norm_mul
          linear_combination h_norm_mul
        rw [← h_circle] at hu_supp
        apply hu_supp
        exact h_div_zero_at_edge (_root_.circleMap e R₀ (u - e).arg)
          (h_arc_mem (u - e).arg h_arg_in) (hg_arc (u - e).arg h_arg_in)
  -- Per-pole F_Y winding = 1.
  have h_per_pole : ∀ u ∈ Dsupp,
      (2 * Real.pi * Complex.I)⁻¹ * (
        (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) +
        (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) +
        Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) -
        Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
        (∫ θ in (0 : ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = 1 := by
    intro u hu
    exact rectMinusUpperHalfDiskWindingNumber_inside_eq_one a b d e R₀ hR₀ hab
      h_a_lt h_lt_b h_e_im_R0_lt_d (hsupp_in_open u hu)
  -- 2πi ≠ 0.
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  -- Express r as Finset product.
  have hD_hfs : (fun u : ℂ => MeromorphicOn.divisor g F u).HasFiniteSupport :=
    hdiv_finite
  have hr_eq_finset : ∀ z, r z =
      ∏ u ∈ Dsupp, (z - u) ^ (MeromorphicOn.divisor g F u) := by
    intro z
    have heq := Function.FactorizedRational.finprod_eq_fun hD_hfs
    have hrz : r z = ∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor g F u) := by
      rw [hr_def, heq]
    rw [hrz]
    rw [finprod_eq_prod_of_mulSupport_subset
      (f := fun u => (z - u) ^ (MeromorphicOn.divisor g F u))
      (s := Dsupp)]
    intro u hu
    simp only [Function.mem_mulSupport, ne_eq] at hu
    change u ∈ hdiv_finite.toFinset
    rw [Set.Finite.mem_toFinset]
    intro h_zero
    apply hu
    rw [h_zero]; simp
  have hzpow_eq_pow : ∀ u : ℂ, ∀ z : ℂ,
      (z - u) ^ (MeromorphicOn.divisor g F u) =
      (z - u) ^ ((MeromorphicOn.divisor g F u).toNat) := by
    intro u z
    rw [← zpow_natCast (z - u) ((MeromorphicOn.divisor g F u).toNat),
        Int.toNat_of_nonneg (hD_nonneg u)]
  have hr_eq_natpow : ∀ z, r z =
      ∏ u ∈ Dsupp, (z - u) ^ ((MeromorphicOn.divisor g F u).toNat) := by
    intro z
    rw [hr_eq_finset z]
    apply Finset.prod_congr rfl
    intro u _
    exact hzpow_eq_pow u z
  -- logDeriv r at boundary points (where g ≠ 0).
  have h_logDeriv_r_eq : ∀ z ∈ F, g z ≠ 0 →
      deriv r z / r z = ∑ u ∈ Dsupp,
        ((MeromorphicOn.divisor g F u : ℂ) / (z - u)) := by
    intro z hz hz_g_ne
    have hz_ne_u : ∀ u ∈ Dsupp, z - u ≠ 0 := by
      intro u hu hzu
      have hz_eq : z = u := by linear_combination hzu
      have hu_supp : u ∈ (MeromorphicOn.divisor g F).support := by
        simpa [hDsupp_def] using hu
      apply hu_supp
      rw [← hz_eq]
      exact h_div_zero_at_edge z hz hz_g_ne
    set D := MeromorphicOn.divisor g F
    have hr_funext_nat : r = fun y => ∏ u ∈ Dsupp, (y - u) ^ ((D u).toNat) := by
      funext y; exact hr_eq_natpow y
    rw [show deriv r z / r z = logDeriv r z from rfl, hr_funext_nat]
    rw [logDeriv_prod]
    · apply Finset.sum_congr rfl
      intro u _
      have hd : DifferentiableAt ℂ (fun w : ℂ => w - u) z := by fun_prop
      rw [show (fun w : ℂ => (w - u) ^ ((D u).toNat)) =
          (fun w : ℂ => (fun w' => w' - u) w ^ ((D u).toNat)) from rfl,
          logDeriv_fun_pow hd, logDeriv_apply]
      have hnat_eq : ((D u).toNat : ℤ) = D u := Int.toNat_of_nonneg (hD_nonneg u)
      have hnat : ((D u).toNat : ℂ) = (D u : ℂ) := by exact_mod_cast hnat_eq
      rw [hnat]
      simp; ring
    · intro u hu
      exact pow_ne_zero _ (hz_ne_u u hu)
    · intro u _
      exact ((differentiable_id.sub_const u).pow _).differentiableAt
  -- Non-vanishing of (z - u) on each edge/arc for u ∈ Dsupp.
  have h_ne_bot_left : ∀ u ∈ Dsupp, ∀ _x : ℝ,
      (_x : ℂ) + (e.im : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu x h_eq
    obtain ⟨hu_box, _⟩ := hsupp_in_open u hu
    rw [Complex.mem_reProdIm] at hu_box
    have hu_im_Ioo : u.im ∈ Set.Ioo e.im d := hu_box.2
    rw [Set.mem_Ioo] at hu_im_Ioo
    have h_im : ((x : ℂ) + (e.im : ℂ) * Complex.I - u).im = e.im - u.im := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_im_eq : e.im - u.im = 0 := by
      have := congrArg Complex.im h_eq; rw [h_im] at this; simpa using this
    linarith [hu_im_Ioo.1]
  have h_ne_top : ∀ u ∈ Dsupp, ∀ _x : ℝ,
      (_x : ℂ) + (d : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu x h_eq
    obtain ⟨hu_box, _⟩ := hsupp_in_open u hu
    rw [Complex.mem_reProdIm] at hu_box
    have hu_im_Ioo : u.im ∈ Set.Ioo e.im d := hu_box.2
    rw [Set.mem_Ioo] at hu_im_Ioo
    have h_im : ((x : ℂ) + (d : ℂ) * Complex.I - u).im = d - u.im := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_im_eq : d - u.im = 0 := by
      have := congrArg Complex.im h_eq; rw [h_im] at this; simpa using this
    linarith [hu_im_Ioo.2]
  have h_ne_right : ∀ u ∈ Dsupp, ∀ _y : ℝ,
      (b : ℂ) + (_y : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu y h_eq
    obtain ⟨hu_box, _⟩ := hsupp_in_open u hu
    rw [Complex.mem_reProdIm] at hu_box
    have hu_re_Ioo : u.re ∈ Set.Ioo a b := hu_box.1
    rw [Set.mem_Ioo] at hu_re_Ioo
    have h_re : ((b : ℂ) + (y : ℂ) * Complex.I - u).re = b - u.re := by
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_re_eq : b - u.re = 0 := by
      have := congrArg Complex.re h_eq; rw [h_re] at this; simpa using this
    linarith [hu_re_Ioo.2]
  have h_ne_left : ∀ u ∈ Dsupp, ∀ _y : ℝ,
      (a : ℂ) + (_y : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu y h_eq
    obtain ⟨hu_box, _⟩ := hsupp_in_open u hu
    rw [Complex.mem_reProdIm] at hu_box
    have hu_re_Ioo : u.re ∈ Set.Ioo a b := hu_box.1
    rw [Set.mem_Ioo] at hu_re_Ioo
    have h_re : ((a : ℂ) + (y : ℂ) * Complex.I - u).re = a - u.re := by
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_re_eq : a - u.re = 0 := by
      have := congrArg Complex.re h_eq; rw [h_re] at this; simpa using this
    linarith [hu_re_Ioo.1]
  have h_ne_arc : ∀ u ∈ Dsupp, ∀ θ : ℝ,
      _root_.circleMap e R₀ θ - u ≠ 0 := by
    intro u hu θ h_eq
    obtain ⟨_, hu_not_closed⟩ := hsupp_in_open u hu
    apply hu_not_closed
    have h_eq' : u = _root_.circleMap e R₀ θ := by linear_combination -h_eq
    rw [Metric.mem_closedBall, Complex.dist_eq, h_eq', _root_.circleMap]
    have h_sub : e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - e =
        (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by ring
    rw [h_sub, norm_mul, Complex.norm_real,
      Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg hR₀.le]
  -- IntervalIntegrable for each summand on each edge/arc.
  have h_summand_int_bot_left : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun x : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / ((x : ℂ) + (e.im : ℂ) * Complex.I - u))
        MeasureTheory.volume a (e.re - R₀) := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun x => h_ne_bot_left u hu x)
  have h_summand_int_bot_right : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun x : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / ((x : ℂ) + (e.im : ℂ) * Complex.I - u))
        MeasureTheory.volume (e.re + R₀) b := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun x => h_ne_bot_left u hu x)
  have h_summand_int_top : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun x : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / ((x : ℂ) + (d : ℂ) * Complex.I - u))
        MeasureTheory.volume a b := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun x : ℝ => ((x : ℂ) + (d : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun x => h_ne_top u hu x)
  have h_summand_int_right : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun y : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / ((b : ℂ) + (y : ℂ) * Complex.I - u))
        MeasureTheory.volume e.im d := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun y : ℝ => ((b : ℂ) + (y : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun y => h_ne_right u hu y)
  have h_summand_int_left : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun y : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / ((a : ℂ) + (y : ℂ) * Complex.I - u))
        MeasureTheory.volume e.im d := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun y => h_ne_left u hu y)
  have h_summand_int_arc : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun θ : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / (_root_.circleMap e R₀ θ - u) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
        MeasureTheory.volume 0 Real.pi := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont1 : Continuous fun θ : ℝ => (_root_.circleMap e R₀ θ - u) := by
      unfold _root_.circleMap
      fun_prop
    have h_cont2 : Continuous fun θ : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / (_root_.circleMap e R₀ θ - u) :=
      continuous_const.div h_cont1 (fun θ => h_ne_arc u hu θ)
    have h_cont3 : Continuous fun θ : ℝ =>
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)) := by fun_prop
    exact h_cont2.mul h_cont3
  -- IntervalIntegrability of r'/r on each edge/arc.
  have hr_diff_global : Differentiable ℂ r := fun z => (hr_analytic z).differentiableAt
  have hr_cont : Continuous r := hr_diff_global.continuous
  have h_dr_cont : Continuous (deriv r) := by
    refine continuous_iff_continuousAt.mpr (fun z => ?_)
    exact (hr_analytic z).deriv.continuousAt
  have h_dr_div_r_int_bot_left : IntervalIntegrable
      (fun x : ℝ => deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I))
      MeasureTheory.volume a (e.re - R₀) := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ x : ℝ, r ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0 := by
      intro x
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_bot_left u hu x))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_bot_right : IntervalIntegrable
      (fun x : ℝ => deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I))
      MeasureTheory.volume (e.re + R₀) b := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ x : ℝ, r ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0 := by
      intro x
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_bot_left u hu x))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_top : IntervalIntegrable
      (fun x : ℝ => deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun x : ℝ => ((x : ℂ) + (d : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ x : ℝ, r ((x : ℂ) + (d : ℂ) * Complex.I) ≠ 0 := by
      intro x
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_top u hu x))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_right : IntervalIntegrable
      (fun y : ℝ => deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume e.im d := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun y : ℝ => ((b : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ y : ℝ, r ((b : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
      intro y
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_right u hu y))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_left : IntervalIntegrable
      (fun y : ℝ => deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume e.im d := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ y : ℝ, r ((a : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
      intro y
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_left u hu y))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_arc : IntervalIntegrable
      (fun θ : ℝ => deriv r (_root_.circleMap e R₀ θ) /
        r (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun θ : ℝ => _root_.circleMap e R₀ θ) := by
      unfold _root_.circleMap; fun_prop
    have h_r_param_ne : ∀ θ : ℝ, r (_root_.circleMap e R₀ θ) ≠ 0 := by
      intro θ
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_arc u hu θ))
    have h_dr_r_param : Continuous fun θ : ℝ =>
        deriv r (_root_.circleMap e R₀ θ) / r (_root_.circleMap e R₀ θ) :=
      (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
    have h_ie_cont : Continuous fun θ : ℝ =>
        Complex.I * R₀ * Complex.exp (Complex.I * θ) := by fun_prop
    exact h_dr_r_param.mul h_ie_cont
  -- IntervalIntegrability of h'/h on each edge/arc.
  have h_dh_div_h_int_bot_left : IntervalIntegrable
      (fun x : ℝ => deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I))
      MeasureTheory.volume a (e.re - R₀) := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I))
        (Set.uIcc a (e.re - R₀)) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun x : ℝ => (x : ℂ) + (e.im : ℂ) * Complex.I)
        (Set.uIcc a (e.re - R₀)) F := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith : a ≤ e.re - R₀)] at hx
      exact h_bot_left_mem x hx
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_bot_right : IntervalIntegrable
      (fun x : ℝ => deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I))
      MeasureTheory.volume (e.re + R₀) b := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I))
        (Set.uIcc (e.re + R₀) b) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun x : ℝ => (x : ℂ) + (e.im : ℂ) * Complex.I)
        (Set.uIcc (e.re + R₀) b) F := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith : e.re + R₀ ≤ b)] at hx
      exact h_bot_right_mem x hx
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_top : IntervalIntegrable
      (fun x : ℝ => deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun x : ℝ => ((x : ℂ) + (d : ℂ) * Complex.I))
        (Set.uIcc a b) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun x : ℝ => (x : ℂ) + (d : ℂ) * Complex.I)
        (Set.uIcc a b) F := by
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      exact h_top_mem x hx
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_right : IntervalIntegrable
      (fun y : ℝ => deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume e.im d := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun y : ℝ => ((b : ℂ) + (y : ℂ) * Complex.I))
        (Set.uIcc e.im d) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun y : ℝ => (b : ℂ) + (y : ℂ) * Complex.I)
        (Set.uIcc e.im d) F := by
      intro y hy
      rw [Set.uIcc_of_le h_e_im_lt_d.le] at hy
      exact h_right_mem y hy
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_left : IntervalIntegrable
      (fun y : ℝ => deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume e.im d := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I))
        (Set.uIcc e.im d) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I)
        (Set.uIcc e.im d) F := by
      intro y hy
      rw [Set.uIcc_of_le h_e_im_lt_d.le] at hy
      exact h_left_mem y hy
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_arc : IntervalIntegrable
      (fun θ : ℝ => deriv h (_root_.circleMap e R₀ θ) /
        h (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      MeasureTheory.volume 0 Real.pi := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun θ : ℝ => _root_.circleMap e R₀ θ)
        (Set.uIcc 0 Real.pi) := by
      apply Continuous.continuousOn
      unfold _root_.circleMap; fun_prop
    have h_param_maps_to : Set.MapsTo (fun θ : ℝ => _root_.circleMap e R₀ θ)
        (Set.uIcc 0 Real.pi) F := by
      intro θ hθ
      rw [Set.uIcc_of_le Real.pi_nonneg] at hθ
      exact h_arc_mem θ hθ
    have h_dh_r_param : ContinuousOn (fun θ : ℝ => deriv h (_root_.circleMap e R₀ θ) /
        h (_root_.circleMap e R₀ θ)) (Set.uIcc 0 Real.pi) :=
      h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
    have h_ie_cont : ContinuousOn (fun θ : ℝ =>
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) (Set.uIcc 0 Real.pi) := by
      apply Continuous.continuousOn; fun_prop
    exact h_dh_r_param.mul h_ie_cont
  -- Per-edge r-integral decomposition.
  have h_bot_left_r_decomp :
      (∫ x in a..(e.re - R₀), deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
        (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise :
        (∫ x in a..(e.re - R₀), deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
          r ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
        (∫ x in a..(e.re - R₀), ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
          ((x : ℂ) + (e.im : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith : a ≤ e.re - R₀)] at hx
      exact h_logDeriv_r_eq _ (h_bot_left_mem x hx) (hg_bot_left x hx)
    rw [h_pointwise, intervalIntegral.integral_finsetSum h_summand_int_bot_left]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_bot_right_r_decomp :
      (∫ x in (e.re + R₀)..b, deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
        (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise :
        (∫ x in (e.re + R₀)..b, deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
          r ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
        (∫ x in (e.re + R₀)..b, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
          ((x : ℂ) + (e.im : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith : e.re + R₀ ≤ b)] at hx
      exact h_logDeriv_r_eq _ (h_bot_right_mem x hx) (hg_bot_right x hx)
    rw [h_pointwise, intervalIntegral.integral_finsetSum h_summand_int_bot_right]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_top_r_decomp :
      (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise :
        (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
          r ((x : ℂ) + (d : ℂ) * Complex.I)) =
        (∫ x in a..b, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
          ((x : ℂ) + (d : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      exact h_logDeriv_r_eq _ (h_top_mem x hx) (hg_top x hx)
    rw [h_pointwise, intervalIntegral.integral_finsetSum h_summand_int_top]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_right_r_decomp :
      (∫ y in e.im..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
        (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise :
        (∫ y in e.im..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
          r ((b : ℂ) + (y : ℂ) * Complex.I)) =
        (∫ y in e.im..d, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
          ((b : ℂ) + (y : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le h_e_im_lt_d.le] at hy
      exact h_logDeriv_r_eq _ (h_right_mem y hy) (hg_right y hy)
    rw [h_pointwise, intervalIntegral.integral_finsetSum h_summand_int_right]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_left_r_decomp :
      (∫ y in e.im..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
        (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise :
        (∫ y in e.im..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
          r ((a : ℂ) + (y : ℂ) * Complex.I)) =
        (∫ y in e.im..d, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
          ((a : ℂ) + (y : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le h_e_im_lt_d.le] at hy
      exact h_logDeriv_r_eq _ (h_left_mem y hy) (hg_left y hy)
    rw [h_pointwise, intervalIntegral.integral_finsetSum h_summand_int_left]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_arc_r_decomp :
      (∫ θ in (0:ℝ)..Real.pi, deriv r (_root_.circleMap e R₀ θ) /
        r (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
        (∫ θ in (0:ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) := by
    have h_pointwise :
        (∫ θ in (0:ℝ)..Real.pi, deriv r (_root_.circleMap e R₀ θ) /
          r (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
        (∫ θ in (0:ℝ)..Real.pi,
          (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
            (_root_.circleMap e R₀ θ - u)) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le Real.pi_nonneg] at hθ
      have h_eq := h_logDeriv_r_eq _ (h_arc_mem θ hθ) (hg_arc θ hθ)
      change deriv r (_root_.circleMap e R₀ θ) / r (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)) =
        (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
          (_root_.circleMap e R₀ θ - u)) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))
      rw [h_eq]
    rw [h_pointwise]
    rw [show (fun θ : ℝ => (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
            (_root_.circleMap e R₀ θ - u)) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
        (fun θ : ℝ => ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
            (_root_.circleMap e R₀ θ - u) *
            (Complex.I * R₀ * Complex.exp (Complex.I * θ))) from by
      funext θ; rw [Finset.sum_mul]]
    rw [intervalIntegral.integral_finsetSum h_summand_int_arc]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    rw [show (fun θ : ℝ => (MeromorphicOn.divisor g F u : ℂ) *
          (_root_.circleMap e R₀ θ - u)⁻¹ *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
        (fun θ : ℝ => (MeromorphicOn.divisor g F u : ℂ) *
          ((_root_.circleMap e R₀ θ - u)⁻¹ *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) from by funext θ; ring]
    exact intervalIntegral.integral_const_mul _ _
  -- Per-pole 6-piece combination = 2πi.
  have h_per_pole_eq : ∀ u ∈ Dsupp,
      (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) +
      (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) +
      Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) -
      Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
      (∫ θ in (0 : ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      2 * Real.pi * Complex.I := by
    intro u hu
    have h := h_per_pole u hu
    have hk : (2 * Real.pi * Complex.I) * ((2 * Real.pi * Complex.I)⁻¹ *
        ((∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) +
        (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) +
        Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) -
        Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
        (∫ θ in (0 : ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))))) =
        (2 * Real.pi * Complex.I) * 1 := by rw [h]
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul, mul_one] at hk
    exact hk
  -- h-pieces sum to 0 (rearrange h_cauchy_h).
  have h_h_sum_zero :
      ((∫ x in a..(e.re - R₀), deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
          h ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
       (∫ x in (e.re + R₀)..b, deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
          h ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
       Complex.I * (∫ y in e.im..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
          h ((b : ℂ) + (y : ℂ) * Complex.I)) -
       (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
          h ((x : ℂ) + (d : ℂ) * Complex.I)) -
       Complex.I * (∫ y in e.im..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
          h ((a : ℂ) + (y : ℂ) * Complex.I)) -
       (∫ θ in (0:ℝ)..Real.pi, deriv h (_root_.circleMap e R₀ θ) /
          h (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = 0 := by
    have := h_cauchy_h
    linear_combination this
  -- Per-edge/arc split: ∫ (r'/r + h'/h) = ∫ r'/r + ∫ h'/h.
  have h_bot_left_split :
      (∫ x in a..(e.re - R₀), deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
      (∫ x in a..(e.re - R₀), deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
      (∫ x in a..(e.re - R₀), deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_bot_left h_dh_div_h_int_bot_left
  have h_bot_right_split :
      (∫ x in (e.re + R₀)..b, deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
      (∫ x in (e.re + R₀)..b, deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
      (∫ x in (e.re + R₀)..b, deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_bot_right h_dh_div_h_int_bot_right
  have h_top_split :
      (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I)) =
      (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I)) +
      (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_top h_dh_div_h_int_top
  have h_right_split :
      (∫ y in e.im..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in e.im..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in e.im..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_right h_dh_div_h_int_right
  have h_left_split :
      (∫ y in e.im..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in e.im..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in e.im..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_left h_dh_div_h_int_left
  have h_arc_split :
      (∫ θ in (0:ℝ)..Real.pi,
        (deriv r (_root_.circleMap e R₀ θ) /
          r (_root_.circleMap e R₀ θ) +
          deriv h (_root_.circleMap e R₀ θ) /
          h (_root_.circleMap e R₀ θ)) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      (∫ θ in (0:ℝ)..Real.pi, deriv r (_root_.circleMap e R₀ θ) /
          r (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) +
      (∫ θ in (0:ℝ)..Real.pi, deriv h (_root_.circleMap e R₀ θ) /
          h (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) := by
    rw [show (fun θ : ℝ => (deriv r (_root_.circleMap e R₀ θ) /
            r (_root_.circleMap e R₀ θ) +
            deriv h (_root_.circleMap e R₀ θ) /
            h (_root_.circleMap e R₀ θ)) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
        (fun θ : ℝ => deriv r (_root_.circleMap e R₀ θ) /
          r (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ)) +
          deriv h (_root_.circleMap e R₀ θ) /
          h (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) from by funext θ; ring]
    exact intervalIntegral.integral_add h_dr_div_r_int_arc h_dh_div_h_int_arc
  -- Convert Finset sum to finsum.
  have h_finset_eq_finsum :
      (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ)) =
      (∑ᶠ u, (MeromorphicOn.divisor g F u : ℂ)) := by
    rw [finsum_eq_sum_of_support_subset _ (s := Dsupp)]
    intro u hu
    change u ∈ hdiv_finite.toFinset
    rw [Set.Finite.mem_toFinset]
    intro hzero
    apply hu
    simp only [Function.mem_support, ne_eq] at hu
    push_cast at hu ⊢
    simp [hzero] at hu
  have h_finsum_int_eq_nat :
      (∑ᶠ u, (MeromorphicOn.divisor g F u : ℂ)) =
      (((∑ᶠ u, MeromorphicOn.divisor g F u).toNat : ℤ) : ℂ) := by
    have h_nonneg : 0 ≤ ∑ᶠ u, MeromorphicOn.divisor g F u :=
      finsum_nonneg (fun u => hD_nonneg u)
    rw [Int.toNat_of_nonneg h_nonneg]
    have hcast := AddMonoidHom.map_finsum (Int.castRingHom ℂ).toAddMonoidHom
      (f := fun u => MeromorphicOn.divisor g F u) hdiv_finite
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Int.coe_castRingHom] at hcast
    rw [← hcast]
  calc (2 * Real.pi * Complex.I)⁻¹ * (
        (∫ x in a..(e.re - R₀), deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
          g ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
        (∫ x in (e.re + R₀)..b, deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
          g ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
        Complex.I * (∫ y in e.im..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
          g ((b : ℂ) + (y : ℂ) * Complex.I)) -
        (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
          g ((x : ℂ) + (d : ℂ) * Complex.I)) -
        Complex.I * (∫ y in e.im..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
          g ((a : ℂ) + (y : ℂ) * Complex.I)) -
        (∫ θ in (0 : ℝ)..Real.pi, deriv g (_root_.circleMap e R₀ θ) /
          g (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))))
      = (2 * Real.pi * Complex.I)⁻¹ * (
        ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
            (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
         (∫ x in a..(e.re - R₀), deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
            h ((x : ℂ) + (e.im : ℂ) * Complex.I))) +
        ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
            (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
         (∫ x in (e.re + R₀)..b, deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
            h ((x : ℂ) + (e.im : ℂ) * Complex.I))) +
        Complex.I * ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
            (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
         (∫ y in e.im..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
            h ((b : ℂ) + (y : ℂ) * Complex.I))) -
        ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
            (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) +
         (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
            h ((x : ℂ) + (d : ℂ) * Complex.I))) -
        Complex.I * ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
            (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
         (∫ y in e.im..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
            h ((a : ℂ) + (y : ℂ) * Complex.I))) -
        ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
            (∫ θ in (0:ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
              (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) +
         (∫ θ in (0:ℝ)..Real.pi, deriv h (_root_.circleMap e R₀ θ) /
            h (_root_.circleMap e R₀ θ) *
            (Complex.I * R₀ * Complex.exp (Complex.I * θ))))) := by
          rw [h_int_bot_left, h_int_bot_right, h_int_top, h_int_right, h_int_left,
              h_int_arc,
              h_bot_left_split, h_bot_right_split, h_top_split, h_right_split,
              h_left_split, h_arc_split,
              h_bot_left_r_decomp, h_bot_right_r_decomp, h_top_r_decomp,
              h_right_r_decomp, h_left_r_decomp, h_arc_r_decomp]
    _ = (((∑ᶠ u, MeromorphicOn.divisor g F u).toNat : ℂ)) := by
          have h_combine :
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
              Complex.I * (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) -
              Complex.I * (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ θ in (0:ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
                    (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) =
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ)) *
                (2 * Real.pi * Complex.I) := by
            simp only [Finset.mul_sum]
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
                ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
                ← Finset.sum_sub_distrib, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro u hu
            have h := h_per_pole_eq u hu
            linear_combination (MeromorphicOn.divisor g F u : ℂ) * h
          rw [show
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
                (∫ x in a..(e.re - R₀), deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
                    h ((x : ℂ) + (e.im : ℂ) * Complex.I))) +
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
                (∫ x in (e.re + R₀)..b, deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
                    h ((x : ℂ) + (e.im : ℂ) * Complex.I))) +
              Complex.I * ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
                (∫ y in e.im..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
                    h ((b : ℂ) + (y : ℂ) * Complex.I))) -
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) +
                (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
                    h ((x : ℂ) + (d : ℂ) * Complex.I))) -
              Complex.I * ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
                (∫ y in e.im..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
                    h ((a : ℂ) + (y : ℂ) * Complex.I))) -
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ θ in (0:ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
                    (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) +
                (∫ θ in (0:ℝ)..Real.pi, deriv h (_root_.circleMap e R₀ θ) /
                  h (_root_.circleMap e R₀ θ) *
                  (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) =
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
                (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
                Complex.I * (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
                (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) -
                Complex.I * (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
                (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ θ in (0:ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
                    (Complex.I * R₀ * Complex.exp (Complex.I * θ))))) +
              ((∫ x in a..(e.re - R₀), deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
                  h ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
                (∫ x in (e.re + R₀)..b, deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
                  h ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
                Complex.I * (∫ y in e.im..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
                  h ((b : ℂ) + (y : ℂ) * Complex.I)) -
                (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
                  h ((x : ℂ) + (d : ℂ) * Complex.I)) -
                Complex.I * (∫ y in e.im..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
                  h ((a : ℂ) + (y : ℂ) * Complex.I)) -
                (∫ θ in (0:ℝ)..Real.pi, deriv h (_root_.circleMap e R₀ θ) /
                  h (_root_.circleMap e R₀ θ) *
                  (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) from by ring]
          rw [h_combine, h_h_sum_zero, add_zero]
          rw [mul_comm ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ))) (2 * Real.pi * Complex.I)]
          rw [inv_mul_cancel_left₀ hpi]
          exact h_finset_eq_finsum.trans (h_finsum_int_eq_nat.trans (by push_cast; rfl))


/-- **Argument principle on the truncated region (existential form).**
The `(2πi)⁻¹`-normalized boundary integral of `g'/g` is a non-negative
integer: the existential weakening of
`cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk`,
which identifies the integer as the divisor sum (total zero count with
multiplicity) of `g` on the region. -/
theorem cIntegralLogDeriv_isNat_of_nonzero_on_rectMinusUpperHalfDisk
    (g : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hab : a < b) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    (hg_bot_left : ∀ x ∈ Set.Icc a (e.re - R₀),
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (e.re + R₀) b,
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc a b, g ((x : ℂ) + (d : ℂ) * Complex.I) ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc e.im d, g ((b : ℂ) + (y : ℂ) * Complex.I) ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc e.im d, g ((a : ℂ) + (y : ℂ) * Complex.I) ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      g (_root_.circleMap e R₀ θ) ≠ 0) :
    ∃ n : ℕ, (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in a..(e.re - R₀), deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        g ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
      (∫ x in (e.re + R₀)..b, deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        g ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
      Complex.I * (∫ y in e.im..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
        g ((b : ℂ) + (y : ℂ) * Complex.I)) -
      (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
        g ((x : ℂ) + (d : ℂ) * Complex.I)) -
      Complex.I * (∫ y in e.im..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
        g ((a : ℂ) + (y : ℂ) * Complex.I)) -
      (∫ θ in (0 : ℝ)..Real.pi, deriv g (_root_.circleMap e R₀ θ) /
        g (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = (n : ℂ) :=
  ⟨_, cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk
    g a b d e R₀ hab hR₀ h_a_lt h_lt_b h_e_im_R0_lt_d hg
    hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc⟩


/-- **Lower bound for the zero count.** If `g` vanishes at a point of
the truncated region (and is nonzero at the bottom-left corner, so its
orders are finite throughout), the total divisor sum is at least one. -/
theorem one_le_divisor_sum_toNat_of_zero_on_rectMinusUpperHalfDisk
    (g : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hab : a < b) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    (h_corner_ne : g ((a : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    {z₀ : ℂ}
    (hz₀_mem : z₀ ∈ (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀)
    (hz₀_zero : g z₀ = 0) :
    1 ≤ (∑ᶠ u, MeromorphicOn.divisor g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) u).toNat := by
  set F : Set ℂ := (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ with hF_def
  have hg_mer : MeromorphicOn g F := hg.meromorphicOn
  have hF_pathConnected : IsPathConnected F :=
    isPathConnected_rectMinusUpperHalfDisk a b d e R₀ hR₀ hab h_a_lt h_lt_b
      h_e_im_R0_lt_d
  have hF_preconn : IsPreconnected F := hF_pathConnected.isConnected.isPreconnected
  have hF_compact : IsCompact F :=
    (IsCompact.reProdIm isCompact_Icc isCompact_Icc).diff Metric.isOpen_ball
  have hdiv_finite : (MeromorphicOn.divisor g F).support.Finite :=
    Function.locallyFinsuppWithin.finiteSupport _ hF_compact
  have hD_nonneg : 0 ≤ MeromorphicOn.divisor g F :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg
  -- The corner is in F and g does not vanish there, so all orders are finite.
  set z₁ : ℂ := (a : ℂ) + (e.im : ℂ) * Complex.I with hz₁_def
  have hz₁_re : z₁.re = a := by
    simp [hz₁_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hz₁_im : z₁.im = e.im := by
    simp [hz₁_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hz₁_in_F : z₁ ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hz₁_re, Set.mem_Icc]; exact ⟨le_refl _, hab.le⟩
      · rw [hz₁_im, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (z₁ - e).re = a - e.re := by
        rw [Complex.sub_re, hz₁_re]
      have h_abs := Complex.abs_re_le_norm (z₁ - e)
      rw [h_re_diff, abs_of_neg (by linarith : a - e.re < 0)] at h_abs
      linarith
  have hz₁_order_ne_top : meromorphicOrderAt g z₁ ≠ ⊤ := by
    rw [(hg z₁ hz₁_in_F).meromorphicOrderAt_eq]
    intro h
    rw [ENat.map_eq_top_iff] at h
    have h0 : analyticOrderAt g z₁ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr h_corner_ne)
    rw [h0] at h
    exact ENat.zero_ne_top h
  have hz₀_order_ne_top : meromorphicOrderAt g z₀ ≠ ⊤ :=
    hg_mer.meromorphicOrderAt_ne_top_of_isPreconnected hF_preconn
      hz₁_in_F hz₀_mem hz₁_order_ne_top
  -- The divisor value at z₀ is at least 1.
  have hD_z₀ : 1 ≤ (MeromorphicOn.divisor g F) z₀ := by
    rw [MeromorphicOn.divisor_apply hg_mer hz₀_mem]
    rw [(hg z₀ hz₀_mem).meromorphicOrderAt_eq] at hz₀_order_ne_top ⊢
    have h_ord_ne_zero : analyticOrderAt g z₀ ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]
      push Not
      exact ⟨hg z₀ hz₀_mem, by simpa using hz₀_zero⟩
    have h_ord_ne_top : analyticOrderAt g z₀ ≠ ⊤ := by
      intro h
      rw [h] at hz₀_order_ne_top
      simp at hz₀_order_ne_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h_ord_ne_top
    have hn_pos : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h1
      · exfalso; apply h_ord_ne_zero; rw [← hn, h0]; rfl
      · exact h1
    rw [← hn, ENat.map_natCast]
    simp only [WithTop.untop₀_coe]
    exact_mod_cast hn_pos
  -- The total divisor sum dominates the single value at z₀.
  have h_single := single_le_finsum z₀
    (hdiv_finite : Function.HasFiniteSupport
      (⇑(MeromorphicOn.divisor g F)))
    (fun u => hD_nonneg u)
  have h_sum_ge : 1 ≤ ∑ᶠ u, (MeromorphicOn.divisor g F) u :=
    le_trans hD_z₀ h_single
  rw [Int.le_toNat (le_trans zero_le_one h_sum_ge)]
  exact_mod_cast h_sum_ge


/-- **Upper bound for the zero count.** If `z₀` is the only possible
zero of `g` on the truncated region and it is simple (nonvanishing
derivative), the total divisor sum is at most one. -/
theorem divisor_sum_toNat_le_one_of_unique_simple_zero_on_rectMinusUpperHalfDisk
    (g : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    {z₀ : ℂ}
    (h_unique : ∀ z ∈ (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀,
      g z = 0 → z = z₀)
    (h_simple : g z₀ = 0 → deriv g z₀ ≠ 0) :
    (∑ᶠ u, MeromorphicOn.divisor g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) u).toNat ≤ 1 := by
  set F : Set ℂ := (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ with hF_def
  have hg_mer : MeromorphicOn g F := hg.meromorphicOn
  -- The divisor vanishes away from z₀.
  have h_supp : ∀ z, z ≠ z₀ → (MeromorphicOn.divisor g F) z = 0 := by
    intro z hz_ne
    by_contra h_ne_zero
    have hz_in_F : z ∈ F :=
      (MeromorphicOn.divisor g F).supportWithinDomain
        (by simpa [Function.mem_support] using h_ne_zero)
    have hg_z_ne : g z ≠ 0 := fun h0 => hz_ne (h_unique z hz_in_F h0)
    apply h_ne_zero
    rw [MeromorphicOn.divisor_apply hg_mer hz_in_F,
      (hg z hz_in_F).meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr hg_z_ne)]
    simp
  have h_sum_eq : (∑ᶠ u, (MeromorphicOn.divisor g F) u) =
      (MeromorphicOn.divisor g F) z₀ :=
    finsum_eq_single _ z₀ h_supp
  rw [h_sum_eq]
  -- The divisor value at z₀ is at most 1.
  by_cases hz₀_in : z₀ ∈ F
  · by_cases hz₀_zero : g z₀ = 0
    · have h_ord : analyticOrderAt g z₀ = 1 :=
        (hg z₀ hz₀_in).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz₀_zero
          (h_simple hz₀_zero)
      rw [MeromorphicOn.divisor_apply hg_mer hz₀_in,
        (hg z₀ hz₀_in).meromorphicOrderAt_eq, h_ord,
        show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, ENat.map_natCast]
      rfl
    · rw [MeromorphicOn.divisor_apply hg_mer hz₀_in,
        (hg z₀ hz₀_in).meromorphicOrderAt_eq,
        analyticOrderAt_eq_zero.mpr (Or.inr hz₀_zero)]
      simp
  · have h_zero : (MeromorphicOn.divisor g F) z₀ = 0 := by
      by_contra h_ne
      exact hz₀_in ((MeromorphicOn.divisor g F).supportWithinDomain
        (by simpa [Function.mem_support] using h_ne))
    rw [h_zero]
    simp


/-- **Two distinct zeros force a zero count of at least two.** If `g`
vanishes at two distinct points of the truncated region (and is nonzero
at the bottom-left corner), the total divisor sum is at least two. -/
theorem two_le_divisor_sum_toNat_of_two_zeros_on_rectMinusUpperHalfDisk
    (g : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hab : a < b) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    (h_corner_ne : g ((a : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    {z₀ z₁ : ℂ} (h_ne : z₀ ≠ z₁)
    (hz₀_mem : z₀ ∈ (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀)
    (hz₀_zero : g z₀ = 0)
    (hz₁_mem : z₁ ∈ (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀)
    (hz₁_zero : g z₁ = 0) :
    2 ≤ (∑ᶠ u, MeromorphicOn.divisor g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) u).toNat := by
  set F : Set ℂ := (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ with hF_def
  have hg_mer : MeromorphicOn g F := hg.meromorphicOn
  have hF_pathConnected : IsPathConnected F :=
    isPathConnected_rectMinusUpperHalfDisk a b d e R₀ hR₀ hab h_a_lt h_lt_b
      h_e_im_R0_lt_d
  have hF_preconn : IsPreconnected F := hF_pathConnected.isConnected.isPreconnected
  have hF_compact : IsCompact F :=
    (IsCompact.reProdIm isCompact_Icc isCompact_Icc).diff Metric.isOpen_ball
  have hdiv_finite : (MeromorphicOn.divisor g F).support.Finite :=
    Function.locallyFinsuppWithin.finiteSupport _ hF_compact
  have hD_nonneg : 0 ≤ MeromorphicOn.divisor g F :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg
  -- The corner is in F and g does not vanish there, so all orders are finite.
  set zc : ℂ := (a : ℂ) + (e.im : ℂ) * Complex.I with hzc_def
  have hzc_re : zc.re = a := by
    simp [hzc_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hzc_im : zc.im = e.im := by
    simp [hzc_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hzc_in_F : zc ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hzc_re, Set.mem_Icc]; exact ⟨le_refl _, hab.le⟩
      · rw [hzc_im, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (zc - e).re = a - e.re := by
        rw [Complex.sub_re, hzc_re]
      have h_abs := Complex.abs_re_le_norm (zc - e)
      rw [h_re_diff, abs_of_neg (by linarith : a - e.re < 0)] at h_abs
      linarith
  have hzc_order_ne_top : meromorphicOrderAt g zc ≠ ⊤ := by
    rw [(hg zc hzc_in_F).meromorphicOrderAt_eq]
    intro h
    rw [ENat.map_eq_top_iff] at h
    have h0 : analyticOrderAt g zc = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr h_corner_ne)
    rw [h0] at h
    exact ENat.zero_ne_top h
  -- Each of the two zeros has divisor value at least 1.
  have hD_ge_one : ∀ z ∈ F, g z = 0 → 1 ≤ (MeromorphicOn.divisor g F) z := by
    intro z hz_mem hz_zero
    have hz_order_ne_top : meromorphicOrderAt g z ≠ ⊤ :=
      hg_mer.meromorphicOrderAt_ne_top_of_isPreconnected hF_preconn
        hzc_in_F hz_mem hzc_order_ne_top
    rw [MeromorphicOn.divisor_apply hg_mer hz_mem]
    rw [(hg z hz_mem).meromorphicOrderAt_eq] at hz_order_ne_top ⊢
    have h_ord_ne_zero : analyticOrderAt g z ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]
      push Not
      exact ⟨hg z hz_mem, by simpa using hz_zero⟩
    have h_ord_ne_top : analyticOrderAt g z ≠ ⊤ := by
      intro h
      rw [h] at hz_order_ne_top
      simp at hz_order_ne_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h_ord_ne_top
    have hn_pos : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h1
      · exfalso; apply h_ord_ne_zero; rw [← hn, h0]; rfl
      · exact h1
    rw [← hn, ENat.map_natCast]
    simp only [WithTop.untop₀_coe]
    exact_mod_cast hn_pos
  -- Sum over the support dominates the two-point sum.
  have h_sum_repr : (∑ᶠ u, (MeromorphicOn.divisor g F) u) =
      ∑ u ∈ hdiv_finite.toFinset, (MeromorphicOn.divisor g F) u := by
    refine finsum_eq_sum_of_support_subset _ ?_
    rw [Set.Finite.coe_toFinset]
  have hz₀_supp : z₀ ∈ hdiv_finite.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    have := hD_ge_one z₀ hz₀_mem hz₀_zero
    omega
  have hz₁_supp : z₁ ∈ hdiv_finite.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    have := hD_ge_one z₁ hz₁_mem hz₁_zero
    omega
  have h_pair_le : ∑ u ∈ ({z₀, z₁} : Finset ℂ), (MeromorphicOn.divisor g F) u ≤
      ∑ u ∈ hdiv_finite.toFinset, (MeromorphicOn.divisor g F) u := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; exact hz₀_supp
      · rw [Finset.mem_singleton.mp h]; exact hz₁_supp
    · intro u _ _
      exact hD_nonneg u
  have h_pair_sum : ∑ u ∈ ({z₀, z₁} : Finset ℂ), (MeromorphicOn.divisor g F) u =
      (MeromorphicOn.divisor g F) z₀ + (MeromorphicOn.divisor g F) z₁ :=
    Finset.sum_pair h_ne
  have h_two_le : 2 ≤ ∑ᶠ u, (MeromorphicOn.divisor g F) u := by
    rw [h_sum_repr]
    calc (2 : ℤ) ≤ (MeromorphicOn.divisor g F) z₀ + (MeromorphicOn.divisor g F) z₁ := by
          have h0 := hD_ge_one z₀ hz₀_mem hz₀_zero
          have h1 := hD_ge_one z₁ hz₁_mem hz₁_zero
          omega
      _ = ∑ u ∈ ({z₀, z₁} : Finset ℂ), (MeromorphicOn.divisor g F) u := h_pair_sum.symm
      _ ≤ _ := h_pair_le
  rw [Int.le_toNat (le_trans (by norm_num) h_two_le)]
  exact_mod_cast h_two_le


/-- **A double zero forces a zero count of at least two.** If `g` and
its derivative both vanish at a point of the truncated region (and `g`
is nonzero at the bottom-left corner), the total divisor sum is at
least two: the analytic order at the point is at least `2` by
`AnalyticAt.analyticOrderAt_deriv_add_one`. -/
theorem two_le_divisor_sum_toNat_of_double_zero_on_rectMinusUpperHalfDisk
    (g : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hab : a < b) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    (h_corner_ne : g ((a : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    {z₀ : ℂ}
    (hz₀_mem : z₀ ∈ (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀)
    (hz₀_zero : g z₀ = 0) (hz₀_deriv : deriv g z₀ = 0) :
    2 ≤ (∑ᶠ u, MeromorphicOn.divisor g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) u).toNat := by
  set F : Set ℂ := (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ with hF_def
  have hg_mer : MeromorphicOn g F := hg.meromorphicOn
  have hF_pathConnected : IsPathConnected F :=
    isPathConnected_rectMinusUpperHalfDisk a b d e R₀ hR₀ hab h_a_lt h_lt_b
      h_e_im_R0_lt_d
  have hF_preconn : IsPreconnected F := hF_pathConnected.isConnected.isPreconnected
  have hF_compact : IsCompact F :=
    (IsCompact.reProdIm isCompact_Icc isCompact_Icc).diff Metric.isOpen_ball
  have hdiv_finite : (MeromorphicOn.divisor g F).support.Finite :=
    Function.locallyFinsuppWithin.finiteSupport _ hF_compact
  have hD_nonneg : 0 ≤ MeromorphicOn.divisor g F :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg
  set zc : ℂ := (a : ℂ) + (e.im : ℂ) * Complex.I with hzc_def
  have hzc_re : zc.re = a := by
    simp [hzc_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hzc_im : zc.im = e.im := by
    simp [hzc_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hzc_in_F : zc ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hzc_re, Set.mem_Icc]; exact ⟨le_refl _, hab.le⟩
      · rw [hzc_im, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (zc - e).re = a - e.re := by
        rw [Complex.sub_re, hzc_re]
      have h_abs := Complex.abs_re_le_norm (zc - e)
      rw [h_re_diff, abs_of_neg (by linarith : a - e.re < 0)] at h_abs
      linarith
  have hzc_order_ne_top : meromorphicOrderAt g zc ≠ ⊤ := by
    rw [(hg zc hzc_in_F).meromorphicOrderAt_eq]
    intro h
    rw [ENat.map_eq_top_iff] at h
    have h0 : analyticOrderAt g zc = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr h_corner_ne)
    rw [h0] at h
    exact ENat.zero_ne_top h
  -- The double zero has divisor value at least 2.
  have hD_z₀ : 2 ≤ (MeromorphicOn.divisor g F) z₀ := by
    have hz_order_ne_top : meromorphicOrderAt g z₀ ≠ ⊤ :=
      hg_mer.meromorphicOrderAt_ne_top_of_isPreconnected hF_preconn
        hzc_in_F hz₀_mem hzc_order_ne_top
    have h_an : AnalyticAt ℂ g z₀ := hg z₀ hz₀_mem
    -- analyticOrderAt g z₀ = analyticOrderAt (deriv g) z₀ + 1 ≥ 2.
    have h_key := h_an.analyticOrderAt_deriv_add_one
    have h_sub_eq : (fun x => g x - g z₀) = g := by
      funext x
      rw [hz₀_zero, sub_zero]
    rw [h_sub_eq] at h_key
    have h_deriv_ord_ne_zero : analyticOrderAt (deriv g) z₀ ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]
      push Not
      exact ⟨h_an.deriv, by simpa using hz₀_deriv⟩
    have h_ord_ge_two : 2 ≤ analyticOrderAt g z₀ := by
      rw [← h_key]
      have h_one_le : 1 ≤ analyticOrderAt (deriv g) z₀ :=
        Order.one_le_iff_ne_zero.mpr h_deriv_ord_ne_zero
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ analyticOrderAt (deriv g) z₀ + 1 :=
            add_le_add h_one_le (le_refl 1)
    rw [MeromorphicOn.divisor_apply hg_mer hz₀_mem]
    rw [(hg z₀ hz₀_mem).meromorphicOrderAt_eq] at hz_order_ne_top ⊢
    have h_ord_ne_top : analyticOrderAt g z₀ ≠ ⊤ := by
      intro h
      rw [h] at hz_order_ne_top
      simp at hz_order_ne_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h_ord_ne_top
    have hn_ge : 2 ≤ n := by
      rw [← hn] at h_ord_ge_two
      exact_mod_cast h_ord_ge_two
    rw [← hn, ENat.map_natCast]
    simp only [WithTop.untop₀_coe]
    exact_mod_cast hn_ge
  have h_single := single_le_finsum z₀
    (hdiv_finite : Function.HasFiniteSupport
      (⇑(MeromorphicOn.divisor g F)))
    (fun u => hD_nonneg u)
  have h_sum_ge : 2 ≤ ∑ᶠ u, (MeromorphicOn.divisor g F) u :=
    le_trans hD_z₀ h_single
  rw [Int.le_toNat (le_trans (by norm_num) h_sum_ge)]
  exact_mod_cast h_sum_ge

end Complex
