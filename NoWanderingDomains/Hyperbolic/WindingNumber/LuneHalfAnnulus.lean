/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.WindingNumber.CircleRectangleWinding

/-! # Cauchy–Goursat on lunes and the half-annulus region

Cauchy–Goursat on the non-rectangular regions arising from the truncated `Γ(2)`
fundamental domain: the upper-left and upper-right lunes (rectangle corner minus a
quarter disk, star-shaped from the outer corner, closed via `starPrimitive` identities),
the rectangle with an upper half-disk removed from the bottom edge (by 5-piece
decomposition into three sub-rectangles plus the two lunes with shared edges
cancelling), and the closed upper half-disk. Concludes with
`rectMinusUpperHalfDiskWindingNumber_inside_eq_one` (winding number `1` around interior
points of the rectangle-minus-half-disk region) and path-connectedness of the closed
region.
-/

namespace Complex
open MeasureTheory

/-- **Cauchy-Goursat for the upper-left lune (rectangle corner minus
upper-left quarter disk).** The "upper-left lune" is the closed region
`(Set.Icc (e.re - R₀) e.re ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀`
— a small region in the upper-left corner of the disk's bounding rectangle,
outside the disk. It is bounded by:
* Left edge: `x = e.re - R₀`, `y ∈ [e.im, e.im + R₀]`.
* Top edge: `y = e.im + R₀`, `x ∈ [e.re - R₀, e.re]`.
* Upper-left quarter arc: `θ ∈ [π/2, π]` of `circleMap e R₀`.

The closed lune is **star-shaped from the outer corner** `(e.re - R₀, e.im + R₀)`
(verified geometrically: for any lune point `(x, y)` the segment to the outer
corner stays outside the disk). For `f` continuous on the closed lune and
complex-differentiable on its open interior, the boundary contour integral
(traversed CCW with the lune interior on the left) equals zero.

This lemma + its top-right mirror power the decomposition proof of
`integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn` (the
F_Y-shape CG): the region splits into three rectangles (closed under
Mathlib's `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`)
plus the two lunes. Shared edges cancel and the lune contributions
provide the upper semicircle integral.

**Hypothesis form.** `Hd` asks for differentiability on the open box
`(Ioo a e.re) × (Ioo e.im d)` minus `closedBall e R₀`, where
`a < e.re - R₀` and `e.im + R₀ < d`. This open set is star-shaped from
the outer corner `V = (e.re - R₀, e.im + R₀)`: the segment from `V` to
any point in the upper-left-of-`e` open region outside `closedBall`
stays outside `closedBall`. At the half-annulus call site, the broader
`Hd` on `(Ioo a b) × (Ioo e.im d)` restricts to this form by `mono`.

**Proof strategy.** Define `F := starPrimitive V f` on the star-shaped
open set `U' := (Ioo a e.re) × (Ioo e.im d) \ closedBall e R₀`. By
`hasDerivAt_starPrimitive`, `F` has derivative `f` on `U'`. The left
and top edge integrals equal `F(B) - F(V)` and `F(T) - F(V)`
respectively by direct parameter substitution in the `starPrimitive`
definition. The arc integral equals `F(B) - F(T)` by an ε-arc
limiting argument: for ε > 0 small, parametrize a slightly outer
ε-arc `z_ε(θ) := e + (R₀+ε) e^{iθ}` on `θ ∈ [π/2 + ε, π - ε]`; both
endpoints lie in `U'`, FTC applies, and the limit ε → 0 recovers the
arc integral on `[π/2, π]` via dominated convergence and continuity
of `F` at `T` and `B`. The three boundary-piece identities telescope
to zero. -/
theorem integral_boundary_topLeftLune_eq_zero_of_continuousOn_of_differentiableOn
    (f : ℂ → ℂ) (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (a d : ℝ) (h_a_lune : a < e.re - R₀) (h_d_lune : e.im + R₀ < d)
    (Hc : ContinuousOn f
      ((Set.Icc (e.re - R₀) e.re ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀))
    (Hd : ∃ R₀' : ℝ, 0 < R₀' ∧ R₀' < R₀ ∧ DifferentiableOn ℂ f
      ((Set.Ioo a e.re ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀')) :
    -Complex.I * (∫ y in e.im..(e.im + R₀), f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I)) -
    (∫ x in (e.re - R₀)..e.re, f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I)) -
    (∫ θ in (Real.pi / 2)..Real.pi, f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := by
  -- Top edge integral via horizontal-segment `starPrimitive` substitution.
  have hF_T :=
    Complex.starPrimitive_horizontal_eq_intervalIntegral f (e.re - R₀) e.re (e.im + R₀)
  -- F(B) via vertical-segment `starPrimitive` substitution (from `y = e.im + R₀`
  -- down to `y = e.im`), then reversing the integration direction.
  have hF_B_raw :=
    Complex.starPrimitive_vertical_eq_intervalIntegral f (e.re - R₀) (e.im + R₀) e.im
  have hF_B :
      Complex.starPrimitive
          ((↑(e.re - R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑(e.re - R₀) : ℂ) + (↑e.im : ℂ) * Complex.I) =
        -Complex.I *
          ∫ y in e.im..(e.im + R₀),
            f ((↑(e.re - R₀) : ℂ) + (↑y : ℂ) * Complex.I) := by
    rw [hF_B_raw, intervalIntegral.integral_symm]
    ring
  -- Arc identity from the dedicated sub-lemma.
  have h_arc :=
    Complex.topLeftLune_arc_integral_eq_starPrimitive_sub
      f e R₀ hR₀ a d h_a_lune h_d_lune Hc Hd
  -- Goal collapses to `F(B) - F(T) - (F(B) - F(T)) = 0` after substitution;
  -- `linear_combination` with coercion normalization closes it.
  linear_combination (norm := (push_cast; ring)) -h_arc + hF_T - hF_B

/-- **Cauchy-Goursat for the upper-right lune (rectangle corner minus
upper-right quarter disk).** The mirror of
`integral_boundary_topLeftLune_eq_zero_of_continuousOn_of_differentiableOn`
across `x = e.re`. The "upper-right lune" is the closed region
`(Set.Icc e.re (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀`,
star-shaped from the outer corner `(e.re + R₀, e.im + R₀)`.

**Hypothesis form.** `Hd` asks for differentiability on
`(Ioo e.re b) × (Ioo e.im d)` minus `closedBall e R₀`, where
`e.re + R₀ < b` and `e.im + R₀ < d` — the upper-right-of-`e` open box
minus the closed disk, star-shaped from `V_R = (e.re + R₀, e.im + R₀)`.
The proof mirrors the top-left case across `x = e.re`. -/
theorem integral_boundary_topRightLune_eq_zero_of_continuousOn_of_differentiableOn
    (f : ℂ → ℂ) (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (b d : ℝ) (h_b_lune : e.re + R₀ < b) (h_d_lune : e.im + R₀ < d)
    (Hc : ContinuousOn f
      ((Set.Icc e.re (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀))
    (Hd : ∃ R₀' : ℝ, 0 < R₀' ∧ R₀' < R₀ ∧ DifferentiableOn ℂ f
      ((Set.Ioo e.re b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀')) :
    Complex.I * (∫ y in e.im..(e.im + R₀), f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I)) -
    (∫ x in e.re..(e.re + R₀), f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I)) -
    (∫ θ in (0:ℝ)..(Real.pi / 2), f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := by
  -- F(T): horizontal substitution from V_R (x = e.re + R₀) to T (x = e.re),
  -- then reverse direction so the integral goes `e.re..(e.re + R₀)`.
  have hF_T_raw :=
    Complex.starPrimitive_horizontal_eq_intervalIntegral f (e.re + R₀) e.re (e.im + R₀)
  have hF_T :
      Complex.starPrimitive
          ((↑(e.re + R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑e.re : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) =
        -∫ x in e.re..(e.re + R₀),
            f ((↑x : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) := by
    rw [hF_T_raw, intervalIntegral.integral_symm]
  -- F(W): vertical substitution from V_R (y = e.im + R₀) down to W (y = e.im),
  -- reversing direction.
  have hF_W_raw :=
    Complex.starPrimitive_vertical_eq_intervalIntegral f (e.re + R₀) (e.im + R₀) e.im
  have hF_W :
      Complex.starPrimitive
          ((↑(e.re + R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑(e.re + R₀) : ℂ) + (↑e.im : ℂ) * Complex.I) =
        -Complex.I *
          ∫ y in e.im..(e.im + R₀),
            f ((↑(e.re + R₀) : ℂ) + (↑y : ℂ) * Complex.I) := by
    rw [hF_W_raw, intervalIntegral.integral_symm]
    ring
  -- Arc identity from the dedicated sub-lemma (mirror of the top-left case).
  have h_arc :=
    Complex.topRightLune_arc_integral_eq_starPrimitive_sub
      f e R₀ hR₀ b d h_b_lune h_d_lune Hc Hd
  -- Goal collapses to `F(T) - F(W) - (F(T) - F(W)) = 0` after substitution.
  linear_combination (norm := (push_cast; ring)) -h_arc - hF_T + hF_W

/-- **Cauchy-Goursat for a rectangle with an upper half-disk removed
from the bottom boundary.** For `f` continuous on the closed region
`(Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀` (the rectangle
`[a, b] × [e.im, d]` with the open upper half of the disk centered at
`e` on the bottom edge removed) and complex-differentiable on its open
interior, the contour integral around the boundary equals zero.

The region is the **truncated `Γ(2)` fundamental domain shape** with
`e.im = 0` (the rectangle's bottom y coincides with the disk center's
imaginary part). The boundary, traversed counter-clockwise (region
interior on the left), consists of:
* Bottom-left cut segment: `(a, e.im) → (e.re − R₀, e.im)`, contributing
  `∫_a^{e.re−R₀} f(x + e.im·i) dx`.
* Upper semicircle (clockwise around the disk center, from
  `(e.re − R₀, e.im)` through `(e.re, e.im + R₀)` to `(e.re + R₀, e.im)`),
  contributing `−∫_0^π f(circleMap e R₀ θ) · (i·R₀·exp(i·θ)) dθ`.
* Bottom-right cut segment: `(e.re + R₀, e.im) → (b, e.im)`, contributing
  `∫_{e.re+R₀}^b f(x + e.im·i) dx`.
* Right edge: `(b, e.im) → (b, d)`, contributing
  `i·∫_{e.im}^d f(b + y·i) dy`.
* Top edge (reversed): `(b, d) → (a, d)`, contributing
  `−∫_a^b f(x + d·i) dx`.
* Left edge (reversed): `(a, d) → (a, e.im)`, contributing
  `−i·∫_{e.im}^d f(a + y·i) dy`.

The region is simply-connected; Cauchy-Goursat for simply-connected
regions then gives zero. The proof uses a 5-piece decomposition into
3 sub-rectangles (Mathlib's rect CG) plus the two top lunes
(`topLeftLune`, `topRightLune`), with shared edges cancelling and the
lune arc contributions combining into the upper semicircle. -/
theorem integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn
    (f : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (_hab : a < b) (h_e_im_d : e.im < d) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d)
    (Hc : ContinuousOn f ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    (Hd : ∃ R₀' : ℝ, 0 < R₀' ∧ R₀' < R₀ ∧ DifferentiableOn ℂ f
      ((Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀')) :
    (∫ x in a..(e.re - R₀), f ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
    (∫ x in (e.re + R₀)..b, f ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
    Complex.I * (∫ y in e.im..d, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
    (∫ x in a..b, f ((x : ℂ) + (d : ℂ) * Complex.I)) -
    Complex.I * (∫ y in e.im..d, f ((a : ℂ) + (y : ℂ) * Complex.I)) -
    (∫ θ in (0:ℝ)..Real.pi, f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := by
  -- Strengthened `Hd` is existential: extract the underlying differentiability
  -- on the slightly enlarged set `(Ioo a b × Ioo e.im d) \ closedBall e R₀'` for
  -- some `R₀' < R₀`. The rectangle Cauchy-Goursat call only needs the original
  -- `closedBall e R₀` form, derived by `mono` from the enlargement. The lune
  -- CG calls take the existential form directly.
  obtain ⟨R₀', hR₀'_pos, hR₀'_lt, Hd'⟩ := Hd
  have Hd_orig : DifferentiableOn ℂ f
      ((Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀) := by
    apply Hd'.mono
    rintro z ⟨hz_box, hz_not_R0⟩
    exact ⟨hz_box, fun hz_R0' =>
      hz_not_R0 (Metric.closedBall_subset_closedBall hR₀'_lt.le hz_R0')⟩
  -- 5-piece decomposition: 3 rectangles + 2 lunes.
  -- All sub-rectangles strictly avoid the disk (distance ≥ R₀ from e via real or
  -- imaginary part of (z - e)).
  -- Step 1: subset inclusions for rect A = [a, e.re-R₀] × [e.im, d].
  have h_A_closed_sub :
      (Set.Icc a (e.re - R₀) ×ℂ Set.Icc e.im d) ⊆
        (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, hz.2⟩
      rw [Set.mem_Icc] at hz ⊢
      exact ⟨hz.1.1, by linarith [hz.1.2]⟩
    · intro h_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_ball
      rw [Set.mem_Icc] at hz
      have h_re_diff : (z - e).re ≤ -R₀ := by
        rw [Complex.sub_re]; linarith [hz.1.2]
      have h_norm_ge : |((z - e).re)| ≤ ‖z - e‖ := Complex.abs_re_le_norm _
      have h_abs : |((z - e).re)| ≥ R₀ := by
        rw [abs_of_nonpos (by linarith : (z - e).re ≤ 0)]; linarith
      linarith
  have h_A_open_sub :
      (Set.Ioo a (e.re - R₀) ×ℂ Set.Ioo e.im d) ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, hz.2⟩
      rw [Set.mem_Ioo] at hz ⊢
      exact ⟨hz.1.1, by linarith [hz.1.2]⟩
    · intro h_ball
      rw [Metric.mem_closedBall, dist_eq_norm] at h_ball
      rw [Set.mem_Ioo] at hz
      have h_re_diff : (z - e).re < -R₀ := by
        rw [Complex.sub_re]; linarith [hz.1.2]
      have h_norm_ge : |((z - e).re)| ≤ ‖z - e‖ := Complex.abs_re_le_norm _
      have h_abs : |((z - e).re)| > R₀ := by
        rw [abs_of_neg (by linarith : (z - e).re < 0)]; linarith
      linarith
  -- Subset inclusions for rect B = [e.re+R₀, b] × [e.im, d].
  have h_B_closed_sub :
      (Set.Icc (e.re + R₀) b ×ℂ Set.Icc e.im d) ⊆
        (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, hz.2⟩
      rw [Set.mem_Icc] at hz ⊢
      exact ⟨by linarith [hz.1.1], hz.1.2⟩
    · intro h_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_ball
      rw [Set.mem_Icc] at hz
      have h_re_diff : (z - e).re ≥ R₀ := by
        rw [Complex.sub_re]; linarith [hz.1.1]
      have h_norm_ge : |((z - e).re)| ≤ ‖z - e‖ := Complex.abs_re_le_norm _
      have h_abs : |((z - e).re)| ≥ R₀ := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (z - e).re)]; linarith
      linarith
  have h_B_open_sub :
      (Set.Ioo (e.re + R₀) b ×ℂ Set.Ioo e.im d) ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, hz.2⟩
      rw [Set.mem_Ioo] at hz ⊢
      exact ⟨by linarith [hz.1.1], hz.1.2⟩
    · intro h_ball
      rw [Metric.mem_closedBall, dist_eq_norm] at h_ball
      rw [Set.mem_Ioo] at hz
      have h_re_diff : (z - e).re > R₀ := by
        rw [Complex.sub_re]; linarith [hz.1.1]
      have h_norm_ge : |((z - e).re)| ≤ ‖z - e‖ := Complex.abs_re_le_norm _
      have h_abs : |((z - e).re)| > R₀ := by
        rw [abs_of_pos (by linarith : (0:ℝ) < (z - e).re)]; linarith
      linarith
  -- Subset inclusions for rect C = [e.re-R₀, e.re+R₀] × [e.im+R₀, d].
  have h_C_closed_sub :
      (Set.Icc (e.re - R₀) (e.re + R₀) ×ℂ Set.Icc (e.im + R₀) d) ⊆
        (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Icc] at hz ⊢
        exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
      · rw [Set.mem_Icc] at hz ⊢
        exact ⟨by linarith [hz.2.1], hz.2.2⟩
    · intro h_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_ball
      rw [Set.mem_Icc] at hz
      have h_im_diff : (z - e).im ≥ R₀ := by
        rw [Complex.sub_im]; linarith [hz.2.1]
      have h_norm_ge : |((z - e).im)| ≤ ‖z - e‖ := Complex.abs_im_le_norm _
      have h_abs : |((z - e).im)| ≥ R₀ := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (z - e).im)]; linarith
      linarith
  have h_C_open_sub :
      (Set.Ioo (e.re - R₀) (e.re + R₀) ×ℂ Set.Ioo (e.im + R₀) d) ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Ioo] at hz ⊢
        exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
      · rw [Set.mem_Ioo] at hz ⊢
        exact ⟨by linarith [hz.2.1], hz.2.2⟩
    · intro h_ball
      rw [Metric.mem_closedBall, dist_eq_norm] at h_ball
      rw [Set.mem_Ioo] at hz
      have h_im_diff : (z - e).im > R₀ := by
        rw [Complex.sub_im]; linarith [hz.2.1]
      have h_norm_ge : |((z - e).im)| ≤ ‖z - e‖ := Complex.abs_im_le_norm _
      have h_abs : |((z - e).im)| > R₀ := by
        rw [abs_of_pos (by linarith : (0:ℝ) < (z - e).im)]; linarith
      linarith
  -- Subset inclusions for lunes D, E (in half-annulus closed and open regions).
  have h_D_closed_sub :
      ((Set.Icc (e.re - R₀) e.re ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀) ⊆
        (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ := by
    intro z ⟨hz_rect, hz_not_ball⟩
    refine ⟨?_, hz_not_ball⟩
    rw [Complex.mem_reProdIm] at hz_rect ⊢
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Icc] at hz_rect ⊢
      exact ⟨by linarith [hz_rect.1.1], by linarith [hz_rect.1.2]⟩
    · rw [Set.mem_Icc] at hz_rect ⊢
      exact ⟨hz_rect.2.1, by linarith [hz_rect.2.2]⟩
  have h_D_open_sub :
      ((Set.Ioo (e.re - R₀) e.re ×ℂ Set.Ioo e.im (e.im + R₀)) \ Metric.closedBall e R₀) ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z ⟨hz_rect, hz_not_cball⟩
    refine ⟨?_, hz_not_cball⟩
    rw [Complex.mem_reProdIm] at hz_rect ⊢
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Ioo] at hz_rect ⊢
      exact ⟨by linarith [hz_rect.1.1], by linarith [hz_rect.1.2]⟩
    · rw [Set.mem_Ioo] at hz_rect ⊢
      exact ⟨hz_rect.2.1, by linarith [hz_rect.2.2]⟩
  -- Subset target for the TOP-LEFT lune CG: the half-annulus
  -- Hd domain `(Ioo a b × Ioo e.im d) \ closedBall` restricts (via mono)
  -- to `(Ioo a e.re × Ioo e.im d) \ closedBall`, which is the star-shaped
  -- open set used in the lune CG proof (star center at `(e.re - R₀, e.im + R₀)`).
  have h_D_lune_Hd_sub :
      (Set.Ioo a e.re ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z ⟨hz_box, hz_not_cball⟩
    refine ⟨?_, hz_not_cball⟩
    rw [Complex.mem_reProdIm] at hz_box ⊢
    refine ⟨?_, hz_box.2⟩
    rw [Set.mem_Ioo] at hz_box ⊢
    exact ⟨hz_box.1.1, by linarith [hz_box.1.2]⟩
  have h_E_closed_sub :
      ((Set.Icc e.re (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀) ⊆
        (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ := by
    intro z ⟨hz_rect, hz_not_ball⟩
    refine ⟨?_, hz_not_ball⟩
    rw [Complex.mem_reProdIm] at hz_rect ⊢
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Icc] at hz_rect ⊢
      exact ⟨by linarith [hz_rect.1.1], by linarith [hz_rect.1.2]⟩
    · rw [Set.mem_Icc] at hz_rect ⊢
      exact ⟨hz_rect.2.1, by linarith [hz_rect.2.2]⟩
  have h_E_open_sub :
      ((Set.Ioo e.re (e.re + R₀) ×ℂ Set.Ioo e.im (e.im + R₀)) \ Metric.closedBall e R₀) ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z ⟨hz_rect, hz_not_cball⟩
    refine ⟨?_, hz_not_cball⟩
    rw [Complex.mem_reProdIm] at hz_rect ⊢
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Ioo] at hz_rect ⊢
      exact ⟨by linarith [hz_rect.1.1], by linarith [hz_rect.1.2]⟩
    · rw [Set.mem_Ioo] at hz_rect ⊢
      exact ⟨hz_rect.2.1, by linarith [hz_rect.2.2]⟩
  -- Subset target for the TOP-RIGHT lune CG: shrink left bound
  -- `a` up to `e.re`, giving `(Ioo e.re b × Ioo e.im d) \ closedBall`, the
  -- star-shaped open set used in the right lune's CG proof (star center at
  -- `(e.re + R₀, e.im + R₀)`).
  have h_E_lune_Hd_sub :
      (Set.Ioo e.re b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z ⟨hz_box, hz_not_cball⟩
    refine ⟨?_, hz_not_cball⟩
    rw [Complex.mem_reProdIm] at hz_box ⊢
    refine ⟨?_, hz_box.2⟩
    rw [Set.mem_Ioo] at hz_box ⊢
    exact ⟨by linarith [hz_box.1.1], hz_box.1.2⟩
  -- Step 2: apply rect CG to A.
  -- Rect endpoints: z = a + e.im·I, w = (e.re-R₀) + d·I.
  have hA_z_re : (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re = a := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hA_z_im : (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im = e.im := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hA_w_re : ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re = e.re - R₀ := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hA_w_im : ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im = d := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hA_Hc : ContinuousOn f
      (Set.uIcc (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re ×ℂ
       Set.uIcc (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im) := by
    rw [hA_z_re, hA_z_im, hA_w_re, hA_w_im,
      Set.uIcc_of_le h_a_lt.le, Set.uIcc_of_le h_e_im_d.le]
    exact Hc.mono h_A_closed_sub
  have hA_Hd : DifferentiableOn ℂ f
      (Set.Ioo (min (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re)
       (max (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re) ×ℂ
       Set.Ioo (min (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im)
       (max (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im)) := by
    rw [hA_z_re, hA_z_im, hA_w_re, hA_w_im,
      min_eq_left h_a_lt.le, max_eq_right h_a_lt.le,
      min_eq_left h_e_im_d.le, max_eq_right h_e_im_d.le]
    exact Hd_orig.mono h_A_open_sub
  have hA := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I)
    ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I) hA_Hc hA_Hd
  rw [hA_z_re, hA_z_im, hA_w_re, hA_w_im] at hA
  simp only [smul_eq_mul] at hA
  -- Step 3: apply rect CG to B.
  have hB_z_re : ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re = e.re + R₀ := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hB_z_im : ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im = e.im := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hB_w_re : (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re = b := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hB_w_im : (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im = d := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hB_Hc : ContinuousOn f
      (Set.uIcc ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re ×ℂ
       Set.uIcc ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im) := by
    rw [hB_z_re, hB_z_im, hB_w_re, hB_w_im,
      Set.uIcc_of_le h_lt_b.le, Set.uIcc_of_le h_e_im_d.le]
    exact Hc.mono h_B_closed_sub
  have hB_Hd : DifferentiableOn ℂ f
      (Set.Ioo (min ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re)
       (max ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re) ×ℂ
       Set.Ioo (min ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im)
       (max ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im)) := by
    rw [hB_z_re, hB_z_im, hB_w_re, hB_w_im,
      min_eq_left h_lt_b.le, max_eq_right h_lt_b.le,
      min_eq_left h_e_im_d.le, max_eq_right h_e_im_d.le]
    exact Hd_orig.mono h_B_open_sub
  have hB := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I)
    (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I) hB_Hc hB_Hd
  rw [hB_z_re, hB_z_im, hB_w_re, hB_w_im] at hB
  simp only [smul_eq_mul] at hB
  -- Step 4: apply rect CG to C.
  have hC_z_re : ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).re
      = e.re - R₀ := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hC_z_im : ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).im
      = e.im + R₀ := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hC_w_re : ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re = e.re + R₀ := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hC_w_im : ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im = d := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_eRm_le_eRp : e.re - R₀ ≤ e.re + R₀ := by linarith
  have hC_Hc : ContinuousOn f
      (Set.uIcc ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).re
        ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re ×ℂ
       Set.uIcc ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).im
        ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im) := by
    rw [hC_z_re, hC_z_im, hC_w_re, hC_w_im,
      Set.uIcc_of_le h_eRm_le_eRp, Set.uIcc_of_le h_e_im_R0_lt_d.le]
    exact Hc.mono h_C_closed_sub
  have hC_Hd : DifferentiableOn ℂ f
      (Set.Ioo (min ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).re
        ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re)
       (max ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).re
        ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re) ×ℂ
       Set.Ioo (min ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).im
        ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im)
       (max ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).im
        ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im)) := by
    rw [hC_z_re, hC_z_im, hC_w_re, hC_w_im,
      min_eq_left h_eRm_le_eRp, max_eq_right h_eRm_le_eRp,
      min_eq_left h_e_im_R0_lt_d.le, max_eq_right h_e_im_R0_lt_d.le]
    exact Hd_orig.mono h_C_open_sub
  have hC := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I)
    ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I) hC_Hc hC_Hd
  rw [hC_z_re, hC_z_im, hC_w_re, hC_w_im] at hC
  simp only [smul_eq_mul] at hC
  -- Step 5: apply lune CG to D, E.
  -- Lune CG hypotheses: each lune CG takes a star-shaped open box
  -- `(Ioo a e.re × Ioo e.im d)` or `(Ioo e.re b × Ioo e.im d)` minus a
  -- slightly shrunken closed ball `closedBall e R₀'` (strengthened form);
  -- this is built from `Hd'` (mono'd to the lune-side box) and the
  -- enlarging existential witness `R₀'`.
  have hD := integral_boundary_topLeftLune_eq_zero_of_continuousOn_of_differentiableOn
    f e R₀ hR₀ a d h_a_lt h_e_im_R0_lt_d
    (Hc.mono h_D_closed_sub)
    ⟨R₀', hR₀'_pos, hR₀'_lt, Hd'.mono (by
      rintro z ⟨hz_box, hz_not_cball⟩
      refine ⟨?_, hz_not_cball⟩
      rw [Complex.mem_reProdIm] at hz_box ⊢
      refine ⟨?_, hz_box.2⟩
      rw [Set.mem_Ioo] at hz_box ⊢
      exact ⟨hz_box.1.1, by linarith [hz_box.1.2]⟩)⟩
  have hE := integral_boundary_topRightLune_eq_zero_of_continuousOn_of_differentiableOn
    f e R₀ hR₀ b d h_lt_b h_e_im_R0_lt_d
    (Hc.mono h_E_closed_sub)
    ⟨R₀', hR₀'_pos, hR₀'_lt, Hd'.mono (by
      rintro z ⟨hz_box, hz_not_cball⟩
      refine ⟨?_, hz_not_cball⟩
      rw [Complex.mem_reProdIm] at hz_box ⊢
      refine ⟨?_, hz_box.2⟩
      rw [Set.mem_Ioo] at hz_box ⊢
      exact ⟨by linarith [hz_box.1.1], hz_box.1.2⟩)⟩
  -- Step 6: continuity on each boundary edge for interval combination.
  -- Continuity on top edge `y = d`.
  have h_top_cont : ContinuousOn (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
      (Set.Icc a b) := by
    have h_inner_cont : Continuous (fun x : ℝ => (x : ℂ) + (d : ℂ) * Complex.I) := by fun_prop
    apply Hc.comp h_inner_cont.continuousOn
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · change ((x : ℂ) + (d : ℂ) * Complex.I).re ∈ Set.Icc a b
        have : ((x : ℂ) + (d : ℂ) * Complex.I).re = x := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact hx
      · change ((x : ℂ) + (d : ℂ) * Complex.I).im ∈ Set.Icc e.im d
        have : ((x : ℂ) + (d : ℂ) * Complex.I).im = d := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact Set.right_mem_Icc.mpr h_e_im_d.le
    · intro h_in_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_in_ball
      have him : ((x : ℂ) + (d : ℂ) * Complex.I - e).im = d - e.im := by
        simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have h_norm_ge : |((x : ℂ) + (d : ℂ) * Complex.I - e).im| ≤
          ‖((x : ℂ) + (d : ℂ) * Complex.I) - e‖ := Complex.abs_im_le_norm _
      rw [him, abs_of_pos (by linarith : (0:ℝ) < d - e.im)] at h_norm_ge
      linarith
  have h_top_int_a_eR : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume a (e.re - R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_a_lt.le]
    apply h_top_cont.mono
    apply Set.Icc_subset_Icc le_rfl
    linarith
  have h_top_int_eRm_eRp : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume (e.re - R₀) (e.re + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_eRm_le_eRp]
    apply h_top_cont.mono
    apply Set.Icc_subset_Icc <;> linarith
  have h_top_int_eRp_b : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume (e.re + R₀) b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_lt_b.le]
    apply h_top_cont.mono
    apply Set.Icc_subset_Icc _ le_rfl
    linarith
  have h_top_combine_left :
      (∫ x in a..(e.re - R₀), f ((x : ℂ) + (d : ℂ) * Complex.I)) +
      (∫ x in (e.re - R₀)..(e.re + R₀), f ((x : ℂ) + (d : ℂ) * Complex.I)) =
      ∫ x in a..(e.re + R₀), f ((x : ℂ) + (d : ℂ) * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals h_top_int_a_eR h_top_int_eRm_eRp
  have h_top_int_a_eRp : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume a (e.re + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : a ≤ e.re + R₀)]
    apply h_top_cont.mono
    apply Set.Icc_subset_Icc le_rfl
    linarith
  have h_top_combine_full :
      (∫ x in a..(e.re + R₀), f ((x : ℂ) + (d : ℂ) * Complex.I)) +
      (∫ x in (e.re + R₀)..b, f ((x : ℂ) + (d : ℂ) * Complex.I)) =
      ∫ x in a..b, f ((x : ℂ) + (d : ℂ) * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals h_top_int_a_eRp h_top_int_eRp_b
  -- Continuity on left edge `x = e.re - R₀`.
  have h_left_lune_cont : ContinuousOn
      (fun y : ℝ => f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I))
      (Set.Icc e.im d) := by
    have h_inner_cont : Continuous (fun y : ℝ => (e.re - R₀ : ℂ) + (y : ℂ) * Complex.I) := by
      fun_prop
    apply Hc.comp h_inner_cont.continuousOn
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · change ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I).re ∈ Set.Icc a b
        have : ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I).re = e.re - R₀ := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re]
        rw [this]; exact ⟨by linarith, by linarith⟩
      · change ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I).im ∈ Set.Icc e.im d
        have : ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I).im = y := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact hy
    · intro h_in_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_in_ball
      have hre : ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I - e).re = -R₀ := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have h_norm_ge : |((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I - e).re| ≤
          ‖((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I) - e‖ := Complex.abs_re_le_norm _
      rw [hre, abs_of_neg (by linarith : -R₀ < 0)] at h_norm_ge
      linarith
  have h_left_int_low : IntervalIntegrable
      (fun y : ℝ => f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume e.im (e.im + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : e.im ≤ e.im + R₀)]
    apply h_left_lune_cont.mono
    apply Set.Icc_subset_Icc le_rfl
    linarith
  have h_left_int_high : IntervalIntegrable
      (fun y : ℝ => f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume (e.im + R₀) d := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_e_im_R0_lt_d.le]
    apply h_left_lune_cont.mono
    apply Set.Icc_subset_Icc _ le_rfl
    linarith
  have h_left_combine :
      (∫ y in e.im..(e.im + R₀), f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in (e.im + R₀)..d, f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y in e.im..d, f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals h_left_int_low h_left_int_high
  -- Continuity on right edge `x = e.re + R₀`.
  have h_right_lune_cont : ContinuousOn
      (fun y : ℝ => f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I))
      (Set.Icc e.im d) := by
    have h_inner_cont : Continuous (fun y : ℝ => (e.re + R₀ : ℂ) + (y : ℂ) * Complex.I) := by
      fun_prop
    apply Hc.comp h_inner_cont.continuousOn
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · change ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I).re ∈ Set.Icc a b
        have : ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I).re = e.re + R₀ := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact ⟨by linarith, by linarith⟩
      · change ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I).im ∈ Set.Icc e.im d
        have : ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I).im = y := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact hy
    · intro h_in_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_in_ball
      have hre : ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I - e).re = R₀ := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have h_norm_ge : |((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I - e).re| ≤
          ‖((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I) - e‖ := Complex.abs_re_le_norm _
      rw [hre, abs_of_pos hR₀] at h_norm_ge
      linarith
  have h_right_int_low : IntervalIntegrable
      (fun y : ℝ => f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume e.im (e.im + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : e.im ≤ e.im + R₀)]
    apply h_right_lune_cont.mono
    apply Set.Icc_subset_Icc le_rfl
    linarith
  have h_right_int_high : IntervalIntegrable
      (fun y : ℝ => f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume (e.im + R₀) d := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_e_im_R0_lt_d.le]
    apply h_right_lune_cont.mono
    apply Set.Icc_subset_Icc _ le_rfl
    linarith
  have h_right_combine :
      (∫ y in e.im..(e.im + R₀), f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in (e.im + R₀)..d, f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y in e.im..d, f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals h_right_int_low h_right_int_high
  -- Continuity on arc (upper semicircle, θ ∈ [0, π]).
  have h_arc_cont : ContinuousOn
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (Set.Icc (0:ℝ) Real.pi) := by
    have h_cm : Continuous (_root_.circleMap e R₀) := continuous_circleMap _ _
    have h_factor_cont : ContinuousOn (fun θ : ℝ =>
        Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Set.Icc (0:ℝ) Real.pi) := Continuous.continuousOn (by fun_prop)
    refine ContinuousOn.mul ?_ h_factor_cont
    -- Show f ∘ circleMap is ContinuousOn [0, π]: each point maps into the closed half-annulus.
    apply Hc.comp h_cm.continuousOn
    intro θ hθ
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show (_root_.circleMap e R₀ θ).re ∈ Set.Icc a b
        have h_re : (_root_.circleMap e R₀ θ).re = e.re + R₀ * Real.cos θ := by
          simp [_root_.circleMap]
        rw [h_re]
        refine ⟨?_, ?_⟩
        · nlinarith [Real.neg_one_le_cos θ]
        · nlinarith [Real.cos_le_one θ]
      · show (_root_.circleMap e R₀ θ).im ∈ Set.Icc e.im d
        have h_im : (_root_.circleMap e R₀ θ).im = e.im + R₀ * Real.sin θ := by
          simp [_root_.circleMap]
        rw [h_im]
        have h_sin_nn : Real.sin θ ≥ 0 := Real.sin_nonneg_of_mem_Icc
          ⟨hθ.1, hθ.2⟩
        refine ⟨?_, ?_⟩
        · nlinarith [h_sin_nn]
        · nlinarith [Real.sin_le_one θ]
    · intro h_ball
      rw [Metric.mem_ball] at h_ball
      have h_sphere : _root_.circleMap e R₀ θ ∈ Metric.sphere e R₀ :=
        _root_.circleMap_mem_sphere e hR₀.le θ
      rw [Metric.mem_sphere] at h_sphere
      linarith
  have h_arc_int_0_half : IntervalIntegrable
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      MeasureTheory.volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2)]
    apply h_arc_cont.mono
    apply Set.Icc_subset_Icc le_rfl
    linarith [Real.pi_pos]
  have h_arc_int_half_pi : IntervalIntegrable
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      MeasureTheory.volume (Real.pi / 2) Real.pi := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)]
    apply h_arc_cont.mono
    apply Set.Icc_subset_Icc _ le_rfl
    linarith [Real.pi_pos]
  have h_arc_combine :
      (∫ θ in (0:ℝ)..(Real.pi / 2), f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) +
      (∫ θ in (Real.pi / 2)..Real.pi, f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      ∫ θ in (0:ℝ)..Real.pi, f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    intervalIntegral.integral_add_adjacent_intervals h_arc_int_0_half h_arc_int_half_pi
  -- Continuity on middle bottom edge `y = e.im + R₀` for adjacent interval combination.
  have h_middle_cont : ContinuousOn
      (fun x : ℝ => f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I))
      (Set.Icc (e.re - R₀) (e.re + R₀)) := by
    have h_inner_cont : Continuous (fun x : ℝ => (x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I) := by
      fun_prop
    apply Hc.comp h_inner_cont.continuousOn
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · change ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I).re ∈ Set.Icc a b
        have : ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I).re = x := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · change ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I).im ∈ Set.Icc e.im d
        have : ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I).im = e.im + R₀ := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact ⟨by linarith, by linarith⟩
    · intro h_in_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_in_ball
      have him : ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I - e).im = R₀ := by
        simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have h_norm_ge : |((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I - e).im| ≤
          ‖((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I) - e‖ := Complex.abs_im_le_norm _
      rw [him, abs_of_pos hR₀] at h_norm_ge
      linarith
  have h_middle_int_left : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I))
      MeasureTheory.volume (e.re - R₀) e.re := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : e.re - R₀ ≤ e.re)]
    apply h_middle_cont.mono
    apply Set.Icc_subset_Icc le_rfl
    linarith
  have h_middle_int_right : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I))
      MeasureTheory.volume e.re (e.re + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : e.re ≤ e.re + R₀)]
    apply h_middle_cont.mono
    apply Set.Icc_subset_Icc _ le_rfl
    linarith
  have h_middle_combine :
      (∫ x in (e.re - R₀)..e.re, f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I)) +
      (∫ x in e.re..(e.re + R₀), f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I)) =
      ∫ x in (e.re - R₀)..(e.re + R₀), f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals h_middle_int_left h_middle_int_right
  -- Step 7: combine A + B + C + D + E + interval combinations. Coercions
  -- `↑(e.re - R₀)` vs `↑e.re - ↑R₀` need to be normalized via `push_cast`.
  linear_combination
    (norm := (push_cast; ring))
    hA + hB + hC + hD + hE + h_top_combine_left + h_top_combine_full +
    h_middle_combine + Complex.I * h_left_combine - Complex.I * h_right_combine + h_arc_combine

/-- **Cauchy-Goursat for the closed upper half-disk
(rectangular-enlargement hypothesis form).** For `f` continuous
on the closed small rectangle `[e.re − R₀, e.re + R₀] × [e.im, e.im + R₀]`
(which contains the closed upper half-disk centered at `e` with radius
`R₀`) and complex-differentiable on a slight rectangular enlargement
`(e.re − R₀ − ε, e.re + R₀ + ε) × (e.im, e.im + R₀ + ε)`, the contour
integral around the boundary of the upper half-disk (bottom diameter
left-to-right + upper semicircle from right to left via top) equals
zero.

This is the easier hypothesis form usable when the integrand is
analytic on a full rectangular neighborhood of the closed small rect
(e.g., for `f` itself in the main F_Y argument-principle theorem, where
the modular function is analytic on the upper half-plane). The proof
combines the two upper lune CGs (`topLeftLune`, `topRightLune`) and
the small rectangle CG via algebraic linear combination: the rect CG
bottom term, the rect CG top + lune top terms, the rect CG vertical
edge terms, and the lune arc terms together collapse into the upper
half-disk identity. -/
theorem integral_boundary_upperHalfDisk_eq_zero_of_continuousOn_of_differentiableOn
    (f : ℂ → ℂ) (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (Hc : ContinuousOn f
      (Set.Icc (e.re - R₀) (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)))
    (Hd : ∃ ε : ℝ, 0 < ε ∧ DifferentiableOn ℂ f
      (Set.Ioo (e.re - R₀ - ε) (e.re + R₀ + ε) ×ℂ
       Set.Ioo e.im (e.im + R₀ + ε))) :
    (∫ x in (e.re - R₀)..(e.re + R₀), f ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
    (∫ θ in (0 : ℝ)..Real.pi, f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := by
  obtain ⟨ε, hε_pos, Hd_box⟩ := Hd
  -- Lune subset for continuity.
  have h_LL_sub : (Set.Icc (e.re - R₀) e.re ×ℂ Set.Icc e.im (e.im + R₀)) \
      Metric.ball e R₀ ⊆
      (Set.Icc (e.re - R₀) (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) := by
    rintro z ⟨hz_box, _⟩
    rw [Complex.mem_reProdIm] at hz_box ⊢
    refine ⟨?_, hz_box.2⟩
    rw [Set.mem_Icc] at hz_box ⊢
    exact ⟨hz_box.1.1, by linarith [hz_box.1.2, hR₀]⟩
  have h_RL_sub : (Set.Icc e.re (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) \
      Metric.ball e R₀ ⊆
      (Set.Icc (e.re - R₀) (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) := by
    rintro z ⟨hz_box, _⟩
    rw [Complex.mem_reProdIm] at hz_box ⊢
    refine ⟨?_, hz_box.2⟩
    rw [Set.mem_Icc] at hz_box ⊢
    exact ⟨by linarith [hz_box.1.1, hR₀], hz_box.1.2⟩
  -- Existential `Hd` for each lune (with R₀' = R₀/2).
  set R₀' := R₀ / 2 with hR₀'_def
  have hR₀'_pos : 0 < R₀' := by simp [hR₀'_def]; linarith
  have hR₀'_lt : R₀' < R₀ := by simp [hR₀'_def]; linarith
  have h_LL_Hd_sub :
      (Set.Ioo (e.re - R₀ - ε) e.re ×ℂ Set.Ioo e.im (e.im + R₀ + ε)) \
        Metric.closedBall e R₀' ⊆
        (Set.Ioo (e.re - R₀ - ε) (e.re + R₀ + ε) ×ℂ
          Set.Ioo e.im (e.im + R₀ + ε)) := by
    rintro z ⟨hz_box, _⟩
    rw [Complex.mem_reProdIm] at hz_box ⊢
    refine ⟨?_, hz_box.2⟩
    rw [Set.mem_Ioo] at hz_box ⊢
    exact ⟨hz_box.1.1, by linarith [hz_box.1.2, hR₀, hε_pos]⟩
  have h_RL_Hd_sub :
      (Set.Ioo e.re (e.re + R₀ + ε) ×ℂ Set.Ioo e.im (e.im + R₀ + ε)) \
        Metric.closedBall e R₀' ⊆
        (Set.Ioo (e.re - R₀ - ε) (e.re + R₀ + ε) ×ℂ
          Set.Ioo e.im (e.im + R₀ + ε)) := by
    rintro z ⟨hz_box, _⟩
    rw [Complex.mem_reProdIm] at hz_box ⊢
    refine ⟨?_, hz_box.2⟩
    rw [Set.mem_Ioo] at hz_box ⊢
    exact ⟨by linarith [hz_box.1.1, hR₀, hε_pos], hz_box.1.2⟩
  -- Apply topLeftLune CG.
  have h_LL := integral_boundary_topLeftLune_eq_zero_of_continuousOn_of_differentiableOn
    f e R₀ hR₀ (e.re - R₀ - ε) (e.im + R₀ + ε) (by linarith) (by linarith)
    (Hc.mono h_LL_sub) ⟨R₀', hR₀'_pos, hR₀'_lt, Hd_box.mono h_LL_Hd_sub⟩
  -- Apply topRightLune CG.
  have h_RL := integral_boundary_topRightLune_eq_zero_of_continuousOn_of_differentiableOn
    f e R₀ hR₀ (e.re + R₀ + ε) (e.im + R₀ + ε) (by linarith) (by linarith)
    (Hc.mono h_RL_sub) ⟨R₀', hR₀'_pos, hR₀'_lt, Hd_box.mono h_RL_Hd_sub⟩
  -- Apply small rect CG.
  have h_re_le : e.re - R₀ ≤ e.re + R₀ := by linarith
  have h_im_le : e.im ≤ e.im + R₀ := by linarith
  have h_rect_Hc : ContinuousOn f
      (Set.uIcc (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I).re ×ℂ
       Set.uIcc (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I).im) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero,
      Complex.I_im, mul_one, sub_self, Complex.mul_im, zero_add]
    rw [Set.uIcc_of_le h_re_le, Set.uIcc_of_le h_im_le]
    exact Hc
  have h_rect_Hd : DifferentiableOn ℂ f
      (Set.Ioo (min (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
          (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I).re)
        (max (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
          (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I).re) ×ℂ
       Set.Ioo (min (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
          (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I).im)
        (max (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
          (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I).im)) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero,
      Complex.I_im, mul_one, sub_self, Complex.mul_im, zero_add,
      min_eq_left h_re_le, max_eq_right h_re_le, min_eq_left h_im_le,
      max_eq_right h_im_le]
    apply Hd_box.mono
    rintro z hz
    rw [Complex.mem_reProdIm] at hz ⊢
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Ioo] at hz ⊢
      exact ⟨by linarith [hz.1.1, hε_pos], by linarith [hz.1.2, hε_pos]⟩
    · rw [Set.mem_Ioo] at hz ⊢
      exact ⟨hz.2.1, by linarith [hz.2.2, hε_pos]⟩
  have h_rect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I)
    (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I) h_rect_Hc h_rect_Hd
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero,
    Complex.I_im, mul_one, sub_self, Complex.mul_im, zero_add,
    smul_eq_mul] at h_rect
  -- Continuity of integrand pieces for interval additivity.
  have h_inner_top_cont : Continuous fun x : ℝ =>
      (x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I := by fun_prop
  have h_top_maps : ∀ x ∈ Set.Icc (e.re - R₀) (e.re + R₀),
      ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I) ∈
        Set.Icc (e.re - R₀) (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀) := by
    intro x hx
    rw [Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero,
        add_zero]
      exact hx
    · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, mul_zero,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, mul_one, zero_add,
        add_zero]
      exact ⟨by linarith, le_refl _⟩
  have h_top_cont : ContinuousOn (fun x : ℝ =>
      f ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I))
      (Set.Icc (e.re - R₀) (e.re + R₀)) :=
    Hc.comp h_inner_top_cont.continuousOn h_top_maps
  have h_top_int_left : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume (e.re - R₀) e.re := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    apply h_top_cont.mono
    intro x hx; exact ⟨hx.1, by linarith [hx.2, hR₀]⟩
  have h_top_int_right : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume e.re (e.re + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    apply h_top_cont.mono
    intro x hx; exact ⟨by linarith [hx.1, hR₀], hx.2⟩
  have h_top_split :
      (∫ x in (e.re - R₀)..(e.re + R₀),
        f ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I)) =
      (∫ x in (e.re - R₀)..e.re,
        f ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I)) +
      (∫ x in e.re..(e.re + R₀),
        f ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I)) :=
    (intervalIntegral.integral_add_adjacent_intervals h_top_int_left h_top_int_right).symm
  -- Continuity for arc.
  have h_circleMap_maps : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      _root_.circleMap e R₀ θ ∈
        Set.Icc (e.re - R₀) (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀) := by
    intro θ hθ
    have h_pi_pos := Real.pi_pos
    have h_cos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have h_cos_ge : Real.cos θ ≥ -1 := Real.neg_one_le_cos θ
    have h_sin_nn : Real.sin θ ≥ 0 :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have h_sin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have h_z_re : (_root_.circleMap e R₀ θ).re = e.re + R₀ * Real.cos θ := by
      rw [_root_.circleMap, Complex.exp_mul_I]
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have h_z_im : (_root_.circleMap e R₀ θ).im = e.im + R₀ * Real.sin θ := by
      rw [_root_.circleMap, Complex.exp_mul_I]
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [h_z_re, Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · have : R₀ * Real.cos θ ≥ R₀ * (-1) :=
          mul_le_mul_of_nonneg_left h_cos_ge hR₀.le
        linarith
      · have : R₀ * Real.cos θ ≤ R₀ * 1 :=
          mul_le_mul_of_nonneg_left h_cos_le hR₀.le
        linarith
    · rw [h_z_im, Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · have : R₀ * Real.sin θ ≥ 0 := mul_nonneg hR₀.le h_sin_nn
        linarith
      · have : R₀ * Real.sin θ ≤ R₀ * 1 :=
          mul_le_mul_of_nonneg_left h_sin_le hR₀.le
        linarith
  have h_arc_cont : ContinuousOn (fun θ : ℝ =>
      f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      (Set.Icc (0 : ℝ) Real.pi) := by
    apply ContinuousOn.mul
    · exact Hc.comp (continuous_circleMap _ _).continuousOn h_circleMap_maps
    · apply Continuous.continuousOn
      exact ((continuous_const.mul continuous_const).mul
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)))
  have h_pi_div_two_le_pi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have h_pi_div_two_nn : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h_arc_int_left : IntervalIntegrable
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      MeasureTheory.volume (0 : ℝ) (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_pi_div_two_nn]
    exact h_arc_cont.mono (fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
  have h_arc_int_right : IntervalIntegrable
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      MeasureTheory.volume (Real.pi / 2) Real.pi := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_pi_div_two_le_pi]
    exact h_arc_cont.mono (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  have h_arc_split :
      (∫ θ in (0 : ℝ)..Real.pi, f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      (∫ θ in (0 : ℝ)..(Real.pi / 2), f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) +
      (∫ θ in (Real.pi / 2)..Real.pi, f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) :=
    (intervalIntegral.integral_add_adjacent_intervals h_arc_int_left h_arc_int_right).symm
  -- Linear-combination assembly.
  linear_combination (norm := (push_cast; ring))
    -h_LL - h_RL + h_rect + h_top_split + h_arc_split

/-- **Cauchy-Goursat for the closed upper half-disk (AnalyticOnNhd
hypothesis form).** For `f` analytic on an open neighborhood of every
point of the closed upper half-disk `closedBall e R₀ ∩ {z : e.im ≤ z.im}`,
the contour integral around the boundary (bottom diameter
left-to-right + upper semicircle from right to left via top) equals
zero.

This is the cleanest hypothesis form, accommodating integrands with
singularities in the rectangular corners outside the half-disk (e.g.,
`1/(z − w)` where `w` is in the upper-corner region inside the closed
small rect but outside the closed disk). Used in the
`rectMinusUpperHalfDiskWindingNumber_inside_eq_one` derivation.

**Proof strategy.** Use compactness of the closed upper half-disk
together with `AnalyticAt.eventually_analyticAt` to extract a uniform
δ > 0 such that the open convex neighborhood
`U := Metric.ball e (R₀ + δ) ∩ {z : z.im > e.im − δ}` is contained in
the analyticity domain. `U` is open (intersection of two open sets)
and convex (intersection of two convex sets); it contains the closed
upper half-disk. Apply `hasDerivAt_starPrimitive` with star center
`p := e + (R₀/2) · I ∈ U` (interior) to get a primitive
`F := starPrimitive p f` with `HasDerivAt F (f z) z` for every `z ∈ U`.
The boundary path of the closed upper half-disk lies in `U` (since
`closedBall ∩ upper half-plane ⊆ U`); FTC gives
`∫_(bottom diameter) f = F((e.re+R₀, e.im)) − F((e.re−R₀, e.im))` and
`∫_(upper semicircle) f = F((e.re−R₀, e.im)) − F((e.re+R₀, e.im))`,
which sum to zero. -/
theorem integral_boundary_upperHalfDisk_eq_zero_of_analyticOnNhd
    (f : ℂ → ℂ) (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (Hf : AnalyticOnNhd ℂ f
      (Metric.closedBall e R₀ ∩ {z : ℂ | e.im ≤ z.im})) :
    (∫ x in (e.re - R₀)..(e.re + R₀), f ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
    (∫ θ in (0 : ℝ)..Real.pi, f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := by
  -- The closed upper half-disk S is compact.
  set S : Set ℂ := Metric.closedBall e R₀ ∩ {z : ℂ | e.im ≤ z.im} with hS_def
  have hS_compact : IsCompact S :=
    (isCompact_closedBall e R₀).inter_right
      (isClosed_le continuous_const Complex.continuous_im)
  -- The analyticity domain V := {z : AnalyticAt ℂ f z} is open and contains S.
  set V : Set ℂ := {z : ℂ | AnalyticAt ℂ f z} with hV_def
  have hV_open : IsOpen V := by
    rw [isOpen_iff_eventually]
    intro z hz
    exact hz.eventually_analyticAt
  have hS_sub_V : S ⊆ V := fun z hz => Hf z hz
  -- Extract uniform δ > 0 with Metric.thickening δ S ⊆ V.
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    hS_compact.exists_thickening_subset_open hV_open hS_sub_V
  -- The convex open thickening U := ball e (R₀ + δ/2) ∩ {z : e.im - δ/2 < z.im}.
  set U : Set ℂ :=
    Metric.ball e (R₀ + δ/2) ∩ {z : ℂ | e.im - δ/2 < z.im} with hU_def
  have hU_open : IsOpen U :=
    Metric.isOpen_ball.inter (isOpen_Ioi.preimage Complex.continuous_im)
  have h_im_linear : IsLinearMap ℝ (fun z : ℂ => z.im) :=
    ⟨fun _ _ => Complex.add_im _ _, fun r z => Complex.smul_im r z⟩
  have hU_convex : Convex ℝ U :=
    (convex_ball _ _).inter (convex_halfSpace_gt h_im_linear (e.im - δ/2))
  -- Show U ⊆ Metric.thickening δ S via projection + radial projection.
  have hU_sub_thickening : U ⊆ Metric.thickening δ S := by
    intro z hz
    obtain ⟨h_ball, h_half⟩ := hz
    rw [Metric.mem_ball, Complex.dist_eq] at h_ball
    change e.im - δ/2 < z.im at h_half
    rw [Metric.mem_thickening_iff]
    by_cases h_above : e.im ≤ z.im
    · -- z.im ≥ e.im: direct or radial projection.
      by_cases h_in_disk : ‖z - e‖ ≤ R₀
      · refine ⟨z, ⟨?_, h_above⟩, by rw [dist_self]; exact hδ_pos⟩
        rw [Metric.mem_closedBall, Complex.dist_eq]; exact h_in_disk
      · push Not at h_in_disk
        have h_norm_pos : 0 < ‖z - e‖ := by linarith
        have h_norm_ne : ‖z - e‖ ≠ 0 := ne_of_gt h_norm_pos
        set s : ℂ := e + ((R₀ / ‖z - e‖ : ℝ) : ℂ) * (z - e) with hs_def
        have hs_sub : s - e = ((R₀ / ‖z - e‖ : ℝ) : ℂ) * (z - e) := by
          rw [hs_def]; ring
        have h_pos_div : (0 : ℝ) ≤ R₀ / ‖z - e‖ :=
          div_nonneg hR₀.le (norm_nonneg _)
        have hs_norm : ‖s - e‖ = R₀ := by
          rw [hs_sub, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg h_pos_div, div_mul_cancel₀ _ h_norm_ne]
        have hs_im : e.im ≤ s.im := by
          have h_diff_im : s.im = e.im + (R₀ / ‖z - e‖) * (z.im - e.im) := by
            rw [hs_def]
            simp [Complex.add_im, Complex.mul_im, Complex.sub_im,
              Complex.ofReal_re, Complex.ofReal_im]
          rw [h_diff_im]
          have h_nn : 0 ≤ R₀ / ‖z - e‖ * (z.im - e.im) :=
            mul_nonneg h_pos_div (by linarith)
          linarith
        have hs_in_S : s ∈ S := by
          refine ⟨?_, hs_im⟩
          rw [Metric.mem_closedBall, Complex.dist_eq, hs_norm]
        refine ⟨s, hs_in_S, ?_⟩
        rw [Complex.dist_eq]
        have h_z_sub : z - s = ((1 - R₀ / ‖z - e‖ : ℝ) : ℂ) * (z - e) := by
          rw [hs_def]; push_cast; field_simp; ring
        have h_one_minus_pos : (0 : ℝ) ≤ 1 - R₀ / ‖z - e‖ := by
          rw [sub_nonneg, div_le_one h_norm_pos]; linarith
        rw [h_z_sub, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg h_one_minus_pos]
        have h_mul_eq : (1 - R₀ / ‖z - e‖) * ‖z - e‖ = ‖z - e‖ - R₀ := by
          field_simp
        linarith [h_mul_eq]
    · -- z.im < e.im: project to z' on bottom diameter, then possibly radially.
      push Not at h_above
      set z' : ℂ := (z.re : ℂ) + (e.im : ℂ) * Complex.I with hz'_def
      have hz'_re : z'.re = z.re := by
        simp [hz'_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have hz'_im : z'.im = e.im := by
        simp [hz'_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have h_dist_z_z' : dist z z' = e.im - z.im := by
        rw [Complex.dist_eq]
        have h_diff : z - z' = ((z.im - e.im : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [hz'_def, Complex.sub_re, Complex.add_re, Complex.mul_re,
              Complex.I_re, Complex.I_im, Complex.ofReal_re,
              Complex.ofReal_im]
          · simp [hz'_def, Complex.sub_im, Complex.add_im, Complex.mul_im,
              Complex.I_re, Complex.I_im, Complex.ofReal_re,
              Complex.ofReal_im]
        rw [h_diff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_neg (by linarith : z.im - e.im < 0)]
        linarith
      have hz'_norm_le_sq : ‖z' - e‖^2 ≤ ‖z - e‖^2 := by
        have h_z'_sq : ‖z' - e‖^2 = (z.re - e.re)^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
            Complex.sub_re, Complex.sub_im, hz'_re, hz'_im]; ring
        have h_z_sq : ‖z - e‖^2 = (z.re - e.re)^2 + (z.im - e.im)^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
            Complex.sub_re, Complex.sub_im]; ring
        nlinarith [sq_nonneg (z.im - e.im), h_z_sq, h_z'_sq]
      have hz'_norm_le : ‖z' - e‖ ≤ ‖z - e‖ := by
        have h_z'_nn : 0 ≤ ‖z' - e‖ := norm_nonneg _
        have h_z_nn : 0 ≤ ‖z - e‖ := norm_nonneg _
        nlinarith [hz'_norm_le_sq, sq_nonneg (‖z - e‖ - ‖z' - e‖),
          sq_nonneg (‖z - e‖ + ‖z' - e‖)]
      by_cases h_z'_in_disk : ‖z' - e‖ ≤ R₀
      · have hz'_in_S : z' ∈ S := by
          refine ⟨?_, ?_⟩
          · rw [Metric.mem_closedBall, Complex.dist_eq]; exact h_z'_in_disk
          · change e.im ≤ z'.im; rw [hz'_im]
        refine ⟨z', hz'_in_S, ?_⟩
        rw [h_dist_z_z']; linarith
      · push Not at h_z'_in_disk
        have h_z'_norm_pos : 0 < ‖z' - e‖ := by linarith
        have h_z'_norm_ne : ‖z' - e‖ ≠ 0 := ne_of_gt h_z'_norm_pos
        set s : ℂ := e + ((R₀ / ‖z' - e‖ : ℝ) : ℂ) * (z' - e) with hs_def
        have hs_sub : s - e = ((R₀ / ‖z' - e‖ : ℝ) : ℂ) * (z' - e) := by
          rw [hs_def]; ring
        have h_pos_div : (0 : ℝ) ≤ R₀ / ‖z' - e‖ :=
          div_nonneg hR₀.le (norm_nonneg _)
        have hs_norm : ‖s - e‖ = R₀ := by
          rw [hs_sub, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg h_pos_div, div_mul_cancel₀ _ h_z'_norm_ne]
        have hs_im : e.im ≤ s.im := by
          have h_diff_im : s.im = e.im + (R₀ / ‖z' - e‖) * (z'.im - e.im) := by
            rw [hs_def]
            simp [Complex.add_im, Complex.mul_im, Complex.sub_im,
              Complex.ofReal_re, Complex.ofReal_im]
          rw [h_diff_im, hz'_im]
          simp
        have hs_in_S : s ∈ S := by
          refine ⟨?_, hs_im⟩
          rw [Metric.mem_closedBall, Complex.dist_eq, hs_norm]
        refine ⟨s, hs_in_S, ?_⟩
        have h_dist_z'_s : dist z' s = ‖z' - e‖ - R₀ := by
          rw [Complex.dist_eq]
          have h_z'_s_sub :
              z' - s = ((1 - R₀ / ‖z' - e‖ : ℝ) : ℂ) * (z' - e) := by
            rw [hs_def]; push_cast; field_simp; ring
          have h_one_minus_pos : (0 : ℝ) ≤ 1 - R₀ / ‖z' - e‖ := by
            rw [sub_nonneg, div_le_one h_z'_norm_pos]; linarith
          rw [h_z'_s_sub, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg h_one_minus_pos]
          have h_mul_eq : (1 - R₀ / ‖z' - e‖) * ‖z' - e‖ = ‖z' - e‖ - R₀ := by
            field_simp
          exact h_mul_eq
        have h_dist_z'_s_lt : dist z' s < δ/2 := by
          rw [h_dist_z'_s]; linarith
        have h_dist_z_z'_lt : dist z z' < δ/2 := by rw [h_dist_z_z']; linarith
        calc dist z s
            ≤ dist z z' + dist z' s := dist_triangle _ _ _
          _ < δ/2 + δ/2 := by linarith
          _ = δ := by ring
  -- U ⊆ V.
  have hU_sub_V : U ⊆ V := fun z hz => hδ_sub (hU_sub_thickening hz)
  -- f differentiable on U.
  have hf_diff_U : DifferentiableOn ℂ f U := fun z hz =>
    (hU_sub_V hz).differentiableAt.differentiableWithinAt
  -- Star center p ∈ U.
  set p : ℂ := e + ((R₀ / 2 : ℝ) : ℂ) * Complex.I with hp_def
  have hp_in_U : p ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have h_diff : p - e = ((R₀ / 2 : ℝ) : ℂ) * Complex.I := by
        rw [hp_def]; ring
      rw [h_diff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
      linarith
    · change e.im - δ/2 < p.im
      have h_p_im : p.im = e.im + R₀/2 := by
        rw [hp_def]
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [h_p_im]; linarith
  have hU_starConvex : StarConvex ℝ p U := hU_convex.starConvex hp_in_U
  -- The primitive F := starPrimitive p f.
  set F : ℂ → ℂ := Complex.starPrimitive p f with hF_def
  have hF_derivAt : ∀ z ∈ U, HasDerivAt F (f z) z := fun z hz =>
    Complex.hasDerivAt_starPrimitive hU_open hU_starConvex hf_diff_U hz
  -- Bottom-diameter path is in U.
  have h_bot_in_U : ∀ x : ℝ, x ∈ Set.Icc (e.re - R₀) (e.re + R₀) →
      ((x : ℂ) + (e.im : ℂ) * Complex.I) ∈ U := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have h_norm_sq :
          ‖((x : ℂ) + (e.im : ℂ) * Complex.I) - e‖^2 = (x - e.re)^2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      have h_x_sq_bound : (x - e.re)^2 ≤ R₀^2 := by
        rw [Set.mem_Icc] at hx; nlinarith [hx.1, hx.2]
      have h_nonneg : 0 ≤ ‖((x : ℂ) + (e.im : ℂ) * Complex.I) - e‖ :=
        norm_nonneg _
      nlinarith [h_norm_sq, h_x_sq_bound, hR₀, hδ_pos]
    · change e.im - δ/2 < ((x : ℂ) + (e.im : ℂ) * Complex.I).im
      have h_im_eq : ((x : ℂ) + (e.im : ℂ) * Complex.I).im = e.im := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [h_im_eq]; linarith
  -- Upper-semicircle path is in U.
  have h_arc_in_U : ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) Real.pi →
      _root_.circleMap e R₀ θ ∈ U := by
    intro θ hθ
    have h_arc_norm : ‖_root_.circleMap e R₀ θ - e‖ = R₀ := by
      rw [_root_.circleMap,
        show e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - e =
          (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) from by ring]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR₀.le,
        Complex.norm_exp_ofReal_mul_I]
      ring
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, h_arc_norm]; linarith
    · change e.im - δ/2 < (_root_.circleMap e R₀ θ).im
      have h_im_eq : (_root_.circleMap e R₀ θ).im = e.im + R₀ * Real.sin θ := by
        rw [_root_.circleMap, Complex.exp_mul_I]
        simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      rw [h_im_eq]
      have h_sin_nn : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
      have h_R_sin_nn : 0 ≤ R₀ * Real.sin θ := mul_nonneg hR₀.le h_sin_nn
      linarith
  -- HasDerivAt of bottom-diameter composition.
  have h_bot_inner_deriv : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => (x : ℂ) + (e.im : ℂ) * Complex.I) 1 x := fun x =>
    (Complex.ofRealCLM.hasDerivAt).add_const _
  have h_G_bot_deriv : ∀ x ∈ Set.Ioo (e.re - R₀) (e.re + R₀),
      HasDerivAt (fun x : ℝ => F ((x : ℂ) + (e.im : ℂ) * Complex.I))
        (f ((x : ℂ) + (e.im : ℂ) * Complex.I)) x := by
    intro x hx
    have hx_Icc : x ∈ Set.Icc (e.re - R₀) (e.re + R₀) := ⟨hx.1.le, hx.2.le⟩
    have h_z_in_U := h_bot_in_U x hx_Icc
    have h_F_at := hF_derivAt _ h_z_in_U
    have h_comp := h_F_at.comp x (h_bot_inner_deriv x)
    simpa using! h_comp
  -- ContinuousOn F on U and f on U.
  have hF_cont_on : ContinuousOn F U := fun z hz =>
    (hF_derivAt z hz).continuousAt.continuousWithinAt
  have hf_cont_on : ContinuousOn f U := fun z hz =>
    (hU_sub_V hz).differentiableAt.continuousAt.continuousWithinAt
  have h_bot_inner_cont :
      Continuous (fun x : ℝ => (x : ℂ) + (e.im : ℂ) * Complex.I) := by fun_prop
  -- ContinuousOn of G_bot.
  have h_G_bot_cont :
      ContinuousOn (fun x : ℝ => F ((x : ℂ) + (e.im : ℂ) * Complex.I))
        (Set.Icc (e.re - R₀) (e.re + R₀)) :=
    hF_cont_on.comp h_bot_inner_cont.continuousOn h_bot_in_U
  -- Integrand continuity on the bottom diameter.
  have h_bot_integrand_cont :
      ContinuousOn (fun x : ℝ => f ((x : ℂ) + (e.im : ℂ) * Complex.I))
        (Set.Icc (e.re - R₀) (e.re + R₀)) :=
    hf_cont_on.comp h_bot_inner_cont.continuousOn h_bot_in_U
  have h_re_le : e.re - R₀ ≤ e.re + R₀ := by linarith
  have h_bot_integrable :
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (e.im : ℂ) * Complex.I))
        MeasureTheory.volume (e.re - R₀) (e.re + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_re_le]
    exact h_bot_integrand_cont
  -- FTC on bottom diameter.
  have h_bot_FTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    h_re_le h_G_bot_cont h_G_bot_deriv h_bot_integrable
  -- HasDerivAt of arc composition.
  have h_arc_inner_deriv : ∀ θ : ℝ,
      HasDerivAt (_root_.circleMap e R₀)
        (_root_.circleMap 0 R₀ θ * Complex.I) θ := fun θ =>
    hasDerivAt_circleMap _ _ _
  have h_arc_deriv_simplify : ∀ θ : ℝ,
      _root_.circleMap 0 R₀ θ * Complex.I =
        Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    intro θ
    rw [_root_.circleMap,
      show ((θ : ℂ) * Complex.I) = Complex.I * (θ : ℂ) from mul_comm _ _]
    ring
  have h_G_arc_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi,
      HasDerivAt (fun θ : ℝ => F (_root_.circleMap e R₀ θ))
        (f (_root_.circleMap e R₀ θ) *
          (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) θ := by
    intro θ hθ
    have hθ_Icc : θ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hθ.1.le, hθ.2.le⟩
    have h_z_in_U := h_arc_in_U θ hθ_Icc
    have h_F_at := hF_derivAt _ h_z_in_U
    have h_comp := h_F_at.comp θ (h_arc_inner_deriv θ)
    rw [h_arc_deriv_simplify] at h_comp
    exact h_comp
  -- ContinuousOn of G_arc.
  have h_G_arc_cont :
      ContinuousOn (fun θ : ℝ => F (_root_.circleMap e R₀ θ))
        (Set.Icc (0 : ℝ) Real.pi) := by
    intro θ hθ
    have h_z_in_U := h_arc_in_U θ hθ
    have h_F_cont_at : ContinuousAt F (_root_.circleMap e R₀ θ) :=
      (hF_derivAt _ h_z_in_U).continuousAt
    have h_circle_cont : Continuous (_root_.circleMap e R₀) :=
      continuous_circleMap _ _
    exact (h_F_cont_at.comp h_circle_cont.continuousAt).continuousWithinAt
  -- Integrand continuity on the arc.
  have h_arc_integrand_cont :
      ContinuousOn (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (Set.Icc (0 : ℝ) Real.pi) := by
    apply ContinuousOn.mul
    · intro θ hθ
      have h_z_in_U := h_arc_in_U θ hθ
      have h_f_cont_at : ContinuousAt f (_root_.circleMap e R₀ θ) :=
        (hU_sub_V h_z_in_U).differentiableAt.continuousAt
      exact (h_f_cont_at.comp
        (continuous_circleMap _ _).continuousAt).continuousWithinAt
    · apply Continuous.continuousOn
      fun_prop
  have h_pi_pos : 0 ≤ Real.pi := Real.pi_pos.le
  have h_arc_integrable :
      IntervalIntegrable (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        MeasureTheory.volume (0 : ℝ) Real.pi := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_pi_pos]
    exact h_arc_integrand_cont
  -- FTC on arc.
  have h_arc_FTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    h_pi_pos h_G_arc_cont h_G_arc_deriv h_arc_integrable
  -- Compute circleMap endpoints.
  have h_circle_pi : _root_.circleMap e R₀ Real.pi =
      ((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I := by
    rw [_root_.circleMap, Complex.exp_mul_I]
    rw [show Complex.cos ((Real.pi : ℂ)) = -1 by
        rw [← Complex.ofReal_cos, Real.cos_pi]; push_cast; ring]
    rw [show Complex.sin ((Real.pi : ℂ)) = 0 by
        rw [← Complex.ofReal_sin, Real.sin_pi]; push_cast; ring]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
    · simp [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have h_circle_0 : _root_.circleMap e R₀ 0 =
      ((e.re + R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I := by
    rw [_root_.circleMap]
    have h_exp_0 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    rw [h_exp_0]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
    · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
  -- Combine.
  rw [h_bot_FTC, h_arc_FTC, h_circle_pi, h_circle_0]
  push_cast
  ring

/-- **F_Y winding number.** The winding number of the F_Y boundary
(rectangle `[a, b] × [e.im, d]` with the upper half-disk centered at
`e` with radius `R₀` removed) around an interior point `w` equals `1`.

The F_Y boundary integral of `(z − w)⁻¹` is `∮_∂rect − ∮_(bottom
diameter) − ∮_(upper semicircle)`. The rect integral equals `2πi` by
`rectangleWindingNumber_inside_eq_one`, and the bottom-diameter plus
upper-semicircle integrals together equal `0` by the upper half-disk
Cauchy-Goursat (since `w` is outside the closed upper half-disk).
Subtraction yields `2πi`, dividing by `2πi` gives `1`. -/
theorem rectMinusUpperHalfDiskWindingNumber_inside_eq_one
    (a b d : ℝ) (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hab : a < b) (_h_a_lt : a < e.re - R₀) (_h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d) {w : ℂ}
    (hw_in : w ∈ (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀) :
    (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
      Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ θ in (0 : ℝ)..Real.pi, (_root_.circleMap e R₀ θ - w)⁻¹ *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = 1 := by
  obtain ⟨hw_box, hw_not_ball⟩ := hw_in
  rw [Complex.mem_reProdIm] at hw_box
  obtain ⟨hw_re_in, hw_im_in⟩ := hw_box
  rw [Set.mem_Ioo] at hw_re_in hw_im_in
  -- w outside closed ball: ‖w - e‖ > R₀.
  have hw_dist_gt : R₀ < ‖w - e‖ := by
    by_contra h
    push Not at h
    exact hw_not_ball (by rw [Metric.mem_closedBall, Complex.dist_eq]; exact h)
  -- e.im < d so we can chain im inequalities.
  have h_e_im_lt_d : e.im < d := by linarith
  -- Step 1: Apply rectangleWindingNumber on the full rectangle.
  have hw_re_pair : a < w.re ∧ w.re < b := hw_re_in
  have hw_im_pair : e.im < w.im ∧ w.im < d := hw_im_in
  have h_rect_wn :=
    rectangleWindingNumber_inside_eq_one a b e.im d hab h_e_im_lt_d hw_re_pair hw_im_pair
  -- 2πi ≠ 0.
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  -- From h_rect_wn, get full rect integral = 2πi.
  have h_rect_eq :
      (∫ x in a..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
      Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) =
      2 * Real.pi * Complex.I := by
    have := h_rect_wn
    have hk : (2 * Real.pi * Complex.I) * ((2 * Real.pi * Complex.I)⁻¹ *
        ((∫ x in a..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
        Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
        Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹))) =
        (2 * Real.pi * Complex.I) * 1 := by rw [this]
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul, mul_one] at hk
    exact hk
  -- Step 2: AnalyticOnNhd of (·-w)⁻¹ on the upper half-disk.
  have h_analytic_inv : AnalyticOnNhd ℂ (fun z : ℂ => (z - w)⁻¹)
      (Metric.closedBall e R₀ ∩ {z : ℂ | e.im ≤ z.im}) := by
    intro z hz
    have hz_in_ball : z ∈ Metric.closedBall e R₀ := hz.1
    have h_dist_z : ‖z - e‖ ≤ R₀ := by
      rw [Metric.mem_closedBall, Complex.dist_eq] at hz_in_ball; exact hz_in_ball
    have h_ne : z - w ≠ 0 := by
      intro h_eq
      have hz_eq : z = w := by linear_combination h_eq
      rw [hz_eq] at h_dist_z
      linarith
    have h_id_an : AnalyticAt ℂ (fun ζ : ℂ => ζ - w) z := by
      exact (analyticAt_id (𝕜 := ℂ)).sub analyticAt_const
    exact h_id_an.inv h_ne
  -- Apply upper half-disk Cauchy-Goursat to (·-w)⁻¹.
  have h_uhd_cg :=
    integral_boundary_upperHalfDisk_eq_zero_of_analyticOnNhd
      (fun z : ℂ => (z - w)⁻¹) e R₀ hR₀ h_analytic_inv
  -- Step 3: Non-vanishing of (x + e.im·I - w) when w.im > e.im.
  have h_ne_bot : ∀ x : ℝ, ((x : ℂ) + (e.im : ℂ) * Complex.I - w) ≠ 0 := by
    intro x h_eq
    have h_im : ((x : ℂ) + (e.im : ℂ) * Complex.I - w).im = e.im - w.im := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
    have h_zero : e.im - w.im = 0 := by
      have := congrArg Complex.im h_eq; rw [h_im] at this; simpa using this
    linarith [hw_im_pair.1]
  -- Step 4: Continuity & interval integrability for (·-w)⁻¹ on the bottom diameter.
  have h_bot_cont : Continuous fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹ := by
    apply Continuous.inv₀
    · fun_prop
    · exact h_ne_bot
  have h_bot_intIntegrable : ∀ p q : ℝ,
      IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹)
        MeasureTheory.volume p q :=
    fun p q => h_bot_cont.intervalIntegrable p q
  -- Step 5: Split full bottom integral via additivity: a → (e.re-R₀) → (e.re+R₀) → b.
  have h_bot_split :
      (∫ x in a..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) =
      (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      (∫ x in (e.re - R₀)..(e.re + R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (h_bot_intIntegrable a (e.re - R₀)) (h_bot_intIntegrable (e.re - R₀) b),
        ← intervalIntegral.integral_add_adjacent_intervals
          (h_bot_intIntegrable (e.re - R₀) (e.re + R₀))
          (h_bot_intIntegrable (e.re + R₀) b)]
    ring
  -- The middle bottom integral equals the upper-half-disk diameter integral.
  -- Step 6: Combine.
  have h_uhd_eq :
      (∫ x in (e.re - R₀)..(e.re + R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      (∫ θ in (0 : ℝ)..Real.pi, (_root_.circleMap e R₀ θ - w)⁻¹ *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := h_uhd_cg
  -- Final calc.
  have h_fY :
      (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
      Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ θ in (0 : ℝ)..Real.pi, (_root_.circleMap e R₀ θ - w)⁻¹ *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      2 * Real.pi * Complex.I := by
    linear_combination h_rect_eq - h_uhd_eq - h_bot_split
  rw [h_fY]
  exact inv_mul_cancel₀ hpi

/-- **Path-connectedness of `F_Y` (closed form).** The closed F_Y region
`(Icc a b ×ℂ Icc e.im d) \ ball e R₀` (rectangle minus upper half of an
open disk centered on the bottom edge) is path-connected. Used to spread
the `MeromorphicOn` order propagation argument in the F_Y argument
principle. -/
theorem isPathConnected_rectMinusUpperHalfDisk
    (a b d : ℝ) (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀) (_hab : a < b)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d) :
    IsPathConnected ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) := by
  set F : Set ℂ := (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ with hF_def
  set p : ℂ := (e.re : ℂ) + (d : ℂ) * Complex.I with hp_def
  have hp_re : p.re = e.re := by
    simp [hp_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hp_im : p.im = d := by
    simp [hp_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  -- p ∉ ball e R₀ because |p - e| = d - e.im > R₀.
  have h_p_dist : R₀ < ‖p - e‖ := by
    have h_im_diff : (p - e).im = d - e.im := by
      simp [hp_def, Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_abs := Complex.abs_im_le_norm (p - e)
    rw [h_im_diff, abs_of_pos (by linarith : (0:ℝ) < d - e.im)] at h_abs
    linarith
  have hp_in : p ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hp_re, Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
      · rw [hp_im, Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; linarith
  refine ⟨p, hp_in, fun z hz => ?_⟩
  obtain ⟨hz_rect, hz_not_ball⟩ := hz
  rw [Complex.mem_reProdIm] at hz_rect
  obtain ⟨hz_re_in, hz_im_in⟩ := hz_rect
  rw [Set.mem_Icc] at hz_re_in hz_im_in
  have hz_dist_ge : R₀ ≤ ‖z - e‖ := by
    by_contra h
    push Not at h
    exact hz_not_ball (Metric.mem_ball.mpr (by rw [Complex.dist_eq]; exact h))
  set mid : ℂ := (z.re : ℂ) + (d : ℂ) * Complex.I with hmid_def
  have hmid_re : mid.re = z.re := by
    simp [hmid_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hmid_im : mid.im = d := by
    simp [hmid_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_mid_dist : R₀ < ‖mid - e‖ := by
    have h_im_diff : (mid - e).im = d - e.im := by
      simp [hmid_def, Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_abs := Complex.abs_im_le_norm (mid - e)
    rw [h_im_diff, abs_of_pos (by linarith : (0:ℝ) < d - e.im)] at h_abs
    linarith
  have hmid_in : mid ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hmid_re, Set.mem_Icc]; exact hz_re_in
      · rw [hmid_im, Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; linarith
  -- JoinedIn F p z via p → mid (horizontal at top) then mid → z (vertical down).
  refine JoinedIn.trans (y := mid) ?_ ?_
  · -- JoinedIn F p mid: horizontal segment at y = d.
    apply JoinedIn.ofLine
      (f := fun t : ℝ => (((1 - t) * e.re + t * z.re : ℝ) : ℂ) + (d : ℂ) * Complex.I)
    · exact (by fun_prop : Continuous fun t : ℝ =>
        (((1 - t) * e.re + t * z.re : ℝ) : ℂ) + (d : ℂ) * Complex.I).continuousOn
    · push_cast; ring
    · push_cast; ring
    · rintro w ⟨t, ht, h_eq⟩
      rw [Set.mem_Icc] at ht
      rw [← h_eq]
      refine ⟨?_, ?_⟩
      · rw [Complex.mem_reProdIm]
        refine ⟨?_, ?_⟩
        · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero,
            add_zero]
          rw [Set.mem_Icc]
          obtain ⟨hz_re_lo, hz_re_hi⟩ := hz_re_in
          refine ⟨?_, ?_⟩
          · nlinarith [ht.1, ht.2, hz_re_lo, h_a_lt, hR₀]
          · nlinarith [ht.1, ht.2, hz_re_hi, h_lt_b, hR₀]
        · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, mul_zero,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, mul_one, zero_add,
            add_zero]
          rw [Set.mem_Icc]
          refine ⟨by linarith, le_refl _⟩
      · rw [Metric.mem_ball, Complex.dist_eq]
        push Not
        have h_im_diff :
            ((((1 - t) * e.re + t * z.re : ℝ) : ℂ) + (d : ℂ) * Complex.I - e).im
              = d - e.im := by
          simp only [Complex.sub_im, Complex.add_im, Complex.mul_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
            mul_zero, mul_one, zero_add, add_zero]
        have h_abs := Complex.abs_im_le_norm
          ((((1 - t) * e.re + t * z.re : ℝ) : ℂ) + (d : ℂ) * Complex.I - e)
        rw [h_im_diff, abs_of_pos (by linarith : (0:ℝ) < d - e.im)] at h_abs
        linarith
  · -- JoinedIn F mid z via vertical segment at x = z.re.
    apply JoinedIn.ofLine
      (f := fun t : ℝ => (z.re : ℂ) + (((1 - t) * d + t * z.im : ℝ) : ℂ) * Complex.I)
    · exact (by fun_prop : Continuous fun t : ℝ =>
        (z.re : ℂ) + (((1 - t) * d + t * z.im : ℝ) : ℂ) * Complex.I).continuousOn
    · show (z.re : ℂ) + (((1 - (0:ℝ)) * d + (0:ℝ) * z.im : ℝ) : ℂ) * Complex.I = mid
      rw [hmid_def]; push_cast; ring
    · show (z.re : ℂ) + (((1 - (1:ℝ)) * d + (1:ℝ) * z.im : ℝ) : ℂ) * Complex.I = z
      push_cast
      apply Complex.ext
      · simp
      · simp
    · rintro w ⟨t, ht, h_eq⟩
      rw [Set.mem_Icc] at ht
      rw [← h_eq]
      refine ⟨?_, ?_⟩
      · rw [Complex.mem_reProdIm]
        refine ⟨?_, ?_⟩
        · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero,
            add_zero]
          rw [Set.mem_Icc]; exact hz_re_in
        · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, mul_zero,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, mul_one, zero_add,
            add_zero]
          rw [Set.mem_Icc]
          obtain ⟨hz_im_lo, hz_im_hi⟩ := hz_im_in
          refine ⟨?_, ?_⟩
          · nlinarith [ht.1, ht.2, hz_im_lo, h_e_im_R0_lt_d, hR₀]
          · nlinarith [ht.1, ht.2, hz_im_hi]
      · rw [Metric.mem_ball, Complex.dist_eq]
        push Not
        -- The point w = (z.re, s) where s = (1-t)·d + t·z.im ∈ [z.im, d].
        -- Squared distance to e: (z.re - e.re)² + (s - e.im)².
        -- s - e.im = (1-t)·(d - e.im) + t·(z.im - e.im). Both terms ≥ z.im - e.im ≥ 0
        -- (first since d > e.im + R₀ > e.im; second since z.im ≥ e.im).
        -- Specifically, s - e.im ≥ z.im - e.im, so (s - e.im)² ≥ (z.im - e.im)².
        -- Hence ‖w - e‖² ≥ (z.re - e.re)² + (z.im - e.im)² = ‖z - e‖² ≥ R₀².
        set s : ℝ := (1 - t) * d + t * z.im with hs_def
        have hs_ge : s ≥ z.im := by nlinarith [ht.1, ht.2, h_e_im_R0_lt_d, hR₀]
        have hs_im_diff_nn : 0 ≤ s - e.im := by linarith [hz_im_in.1]
        have hz_im_diff_nn : 0 ≤ z.im - e.im := by linarith [hz_im_in.1]
        have hw_re : ((z.re : ℂ) + ((s : ℝ) : ℂ) * Complex.I - e).re = z.re - e.re := by
          simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have hw_im : ((z.re : ℂ) + ((s : ℝ) : ℂ) * Complex.I - e).im = s - e.im := by
          simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have h_norm_sq_w : ‖(z.re : ℂ) + ((s : ℝ) : ℂ) * Complex.I - e‖^2 =
            (z.re - e.re)^2 + (s - e.im)^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hw_re, hw_im]
          ring
        have h_norm_sq_z : ‖z - e‖^2 = (z.re - e.re)^2 + (z.im - e.im)^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
              Complex.sub_re, Complex.sub_im]
          ring
        have h_sq_compare : (s - e.im)^2 ≥ (z.im - e.im)^2 := by
          have h1 : s - e.im ≥ z.im - e.im := by linarith
          nlinarith [hs_im_diff_nn, hz_im_diff_nn, h1]
        have h_z_sq_ge : ‖z - e‖^2 ≥ R₀^2 := by
          nlinarith [hz_dist_ge, norm_nonneg (z - e), hR₀.le]
        have h_wn_sq_ge :
            ‖(z.re : ℂ) + ((s : ℝ) : ℂ) * Complex.I - e‖^2 ≥ R₀^2 := by
          linarith [h_norm_sq_w, h_norm_sq_z, h_sq_compare]
        have h_wn_nn : 0 ≤ ‖(z.re : ℂ) + ((s : ℝ) : ℂ) * Complex.I - e‖ :=
          norm_nonneg _
        have h_sqrt := Real.sqrt_le_sqrt h_wn_sq_ge
        rw [Real.sqrt_sq hR₀.le, Real.sqrt_sq h_wn_nn] at h_sqrt
        exact h_sqrt

end Complex
