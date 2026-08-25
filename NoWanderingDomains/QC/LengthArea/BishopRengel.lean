/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Geometric
import NoWanderingDomains.QC.Defs.SensePreserving
import NoWanderingDomains.QC.LengthArea.ReverseLengthAreaForward
import NoWanderingDomains.QC.GeometricToAnalytic.GeometricDifferentiable.Primitives
import NoWanderingDomains.QC.GeometricToAnalytic.GeometricDifferentiable.ReciprocityAssembly
import NoWanderingDomains.QC.InverseQC.SliceAC

/-!
# Rengel-type bricks for the forward length–area theory of geometric QC maps

Shared quantitative bricks for the classical Lehto–Virtanen / Ahlfors / Bishop analysis of a
geometric `K`-quasiconformal homeomorphism `f : ℂ → ℂ` along axis-parallel rectangles:

* **Two-sided modulus bounds** for the image crossing and separating curve families of an
  *arbitrary* axis rectangle (`axisRect_imageModulus_ge`, `axisRectSwap_imageModulus_ge`).
  The upper bounds are the geometric hypothesis itself; the *lower* bounds are manufactured
  from the conjugate-image modulus reciprocity `conjugateImageModulus_reciprocity` (which
  holds for every homeomorphism and every axis rectangle) applied against the upper bound on
  the conjugate family.
* **The flat-density (Rengel) separation bound** for a general quadrilateral's image family
  (`imageCurveFamily_sep_sq_mul_modulus_le_volume`) and the resulting **chord–area
  estimates**: for arbitrary rectangles with side-set separation
  (`qc_sep_sq_le_imageArea_horizontal`/`_vertical`) and for thin strips with the separation
  stated on the parametrized edges (`AxisRectModulusBound.horizontal_strip_sep_sq_le`/
  `AxisRectModulusBound.vertical_strip_sep_sq_le`).
* **The monotone image-area profiles** `imageAreaProfileY`/`imageAreaProfileX` — the
  classical monotone area function `A(y) = area (f '' ([α,β] × [σ,y]))` — with their
  monotonicity, strip-increment, and derivative-mass lemmas.
* **Countability of segments with non-null image**
  (`countable_pos_volume_image_horizontalSeg`/`_verticalSeg`).

These bricks isolate all the genuinely two-dimensional content of the forward (easy)
direction of the reverse length–area theorem; everything downstream of them is finite
combinatorics, one-dimensional real analysis, and `ℝ≥0∞` bookkeeping.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace NoWanderingDomains

/-! ## Compactness helpers -/

/-- **The closed axis rectangle is compact.** `axisRect a b s t = [a,b] × [s,t]` is the image
of the compact product `Icc a b ×ˢ Icc s t` under the (continuous) coordinate embedding
`(x, y) ↦ x + y·I`. The statement covers all degenerate parameter choices: for `b < a` or
`t < s` the rectangle is empty, and for `s = t` it is a horizontal segment. -/
theorem isCompact_axisRect (a b s t : ℝ) : IsCompact (axisRect a b s t) := by
  have himg : axisRect a b s t
      = (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) '' (Set.Icc a b ×ˢ Set.Icc s t) := by
    ext z
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨(z.re, z.im), ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩
    · rintro ⟨p, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  rw [himg]
  refine (isCompact_Icc.prod isCompact_Icc).image ?_
  have h2 : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
      = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    funext p; apply Complex.ext <;> simp
  rw [h2]
  exact (Complex.continuous_ofReal.comp continuous_fst).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

/-- **The image region of a quadrilateral is compact**: it is the continuous image of the
closed unit square. Consequently, for continuous `f` the set `f '' Q.image` is compact,
hence closed, measurable, and of finite Lebesgue measure. -/
theorem Quadrilateral.isCompact_image (Q : Quadrilateral) : IsCompact Q.image := by
  have h : Q.image = Q.toFun '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1) := rfl
  rw [h]
  exact (isCompact_Icc.prod isCompact_Icc).image Q.continuous_toFun

/-! ## The conversion from the geometric hypothesis to the axis-rectangle bound

The whole Bishop chain below is stated over the parametrized hypothesis
`AxisRectModulusBound f K` (`QC/LengthArea/ReverseLengthAreaForward.lean`): `1 ≤ K`,
`IsHomeomorph f`, and the two axis-rectangle image-modulus bounds. The conversion
`IsQCGeometric.toAxisRectModulusBound` supplies the instance for every geometric
`K`-quasiconformal map, so all downstream consumers of the chain keep their
`IsQCGeometric`-flavoured statements as thin wrappers. -/

/-- **A geometric `K`-quasiconformal map satisfies the axis-rectangle modulus bounds.** The
crossing bound is `axisRect_imageModulus_le_ofReal` (the geometric hypothesis at the standard
rectangle parametrization together with the exact rectangle modulus `axisRect_modulus`); the
separating bound is the geometric hypothesis at the swapped parametrization together with the
Rengel upper bound `axisRectSwap_modulus_upper_bound` for the swapped source modulus. -/
theorem IsQCGeometric.toAxisRectModulusBound {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    AxisRectModulusBound f K := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hf.1
  refine ⟨hf.1, hf.2.1.isHomeomorph, ?_, ?_⟩
  · intro a b s t hab hst
    exact axisRect_imageModulus_le_ofReal hf hab hst
  · intro a b s t hab hst
    have hmod := hf.2.2 (axisRectQuadrilateralSwap a b s t hab hst)
    calc curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)
        ≤ ENNReal.ofReal K * (axisRectQuadrilateralSwap a b s t hab hst).modulus := hmod
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal ((b - a) / (t - s)) := by
          gcongr
          exact axisRectSwap_modulus_upper_bound hab hst
      _ = ENNReal.ofReal (K * ((b - a) / (t - s))) := (ENNReal.ofReal_mul hK0).symm

/-! ## Two-sided modulus bounds for image families of arbitrary axis rectangles

The axis-rectangle hypothesis gives only the one-sided upper bounds
`M(f(R)) ≤ K · M(R)`. The lower bounds below are obtained from the reciprocity
`1 ≤ M(Γ) · M(Γ*)` between the image crossing family `Γ` and the image separating family
`Γ*` of the same rectangle, by applying the upper bound to the *conjugate* family
and inverting in `ℝ≥0∞`. This replaces the two-sided modulus quasi-invariance of the
classical treatments (the step `M(R'ⱼ) ≥ M(Rⱼ)/K`). -/

/-- **Crossing-modulus lower bound for the image family of an arbitrary axis rectangle.**
For a map `f` with `AxisRectModulusBound f K` and the rectangle `[a,b] × [s,t]`, the image
crossing family — all absolutely continuous curves joining `f '' ({a} × [s,t])` to
`f '' ({b} × [s,t])` inside `f '' ([a,b] × [s,t])` — has modulus at least
`(t − s)/(K·(b − a))`.

*Proof sketch.* Write `M` for the crossing modulus and `N` for the modulus of the image
*separating* family (the swapped quadrilateral `axisRectQuadrilateralSwap`). The
conjugate-image reciprocity `conjugateImageModulus_reciprocity` (valid for any homeomorphism
and any axis rectangle) gives `1 ≤ M * N`. The separating hypothesis
`hf.axisRectSwap_le` yields `N ≤ ENNReal.ofReal K * ENNReal.ofReal ((b−a)/(t−s))`,
a finite bound which is moreover nonzero (else `1 ≤ 0`). Hence `M ≥ N⁻¹ ≥` the stated
constant, by `ℝ≥0∞` inversion arithmetic (`ENNReal.ofReal_div_of_pos`,
`ENNReal.ofReal_inv_of_pos`, with `0 < K` from `hf.1 : 1 ≤ K`). The proved
`square_imageCurveFamily_modulus_ge` is this argument specialized to squares, where the
aspect-ratio factor `(b−a)/(t−s)` collapses to `1`; here the factor is kept.
-/
theorem axisRect_imageModulus_ge {f : ℂ → ℂ} {K : ℝ} (hf : AxisRectModulusBound f K)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    ENNReal.ofReal ((t - s) / (K * (b - a)))
      ≤ curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f) := by
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hf.1
  have hbma : (0 : ℝ) < b - a := by linarith
  have htms : (0 : ℝ) < t - s := by linarith
  have hfhomeo : IsHomeomorph f := hf.2.1
  set M := curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f) with hM
  set N := curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f) with hN
  -- `N ≤ K · (b−a)/(t−s)`: the separating axis-rectangle bound.
  have hNK : N ≤ ENNReal.ofReal K * ENNReal.ofReal ((b - a) / (t - s)) :=
    hf.axisRectSwap_le hab hst
  -- Reciprocity `1 ≤ M · N`.
  have hrecip : 1 ≤ M * N := conjugateImageModulus_reciprocity hfhomeo hab hst
  -- Chain: `1 ≤ M · N ≤ M · (K · (b−a)/(t−s))`.
  have hchain : (1 : ℝ≥0∞) ≤ M * (ENNReal.ofReal K * ENNReal.ofReal ((b - a) / (t - s))) :=
    le_trans hrecip (by gcongr)
  -- The stated constant is the exact inverse of the bound on `N`.
  have hcancel : ENNReal.ofReal ((t - s) / (K * (b - a)))
      * (ENNReal.ofReal K * ENNReal.ofReal ((b - a) / (t - s))) = 1 := by
    have hK0 : K ≠ 0 := ne_of_gt hKpos
    have hb0 : b - a ≠ 0 := ne_of_gt hbma
    have ht0 : t - s ≠ 0 := ne_of_gt htms
    rw [← ENNReal.ofReal_mul hKpos.le,
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (t - s) / (K * (b - a)))]
    rw [show (t - s) / (K * (b - a)) * (K * ((b - a) / (t - s))) = 1 by field_simp]
    exact ENNReal.ofReal_one
  have hmul : ENNReal.ofReal ((t - s) / (K * (b - a))) * 1
      ≤ ENNReal.ofReal ((t - s) / (K * (b - a)))
        * (M * (ENNReal.ofReal K * ENNReal.ofReal ((b - a) / (t - s)))) := by gcongr
  have hrw : ENNReal.ofReal ((t - s) / (K * (b - a)))
      * (M * (ENNReal.ofReal K * ENNReal.ofReal ((b - a) / (t - s)))) = M := by
    rw [show M * (ENNReal.ofReal K * ENNReal.ofReal ((b - a) / (t - s)))
        = (ENNReal.ofReal K * ENNReal.ofReal ((b - a) / (t - s))) * M from mul_comm _ _,
      ← mul_assoc, hcancel, one_mul]
  rwa [mul_one, hrw] at hmul

/-- **Separating-modulus lower bound for the image family of an arbitrary axis rectangle.**
Mirror of `axisRect_imageModulus_ge`: the image separating family — all absolutely
continuous curves joining `f '' ([a,b] × {s})` to `f '' ([a,b] × {t})` inside
`f '' ([a,b] × [s,t])` — has modulus at least `(b − a)/(K·(t − s))`.

*Proof sketch.* Same reciprocity `1 ≤ M * N` (`conjugateImageModulus_reciprocity`), now
bounding the *crossing* factor by `hf.axisRect_le hab hst :
M ≤ ENNReal.ofReal K * ENNReal.ofReal ((t−s)/(b−a))` and inverting onto the separating
factor `N` with the same `ℝ≥0∞` arithmetic.
-/
theorem axisRectSwap_imageModulus_ge {f : ℂ → ℂ} {K : ℝ} (hf : AxisRectModulusBound f K)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    ENNReal.ofReal ((b - a) / (K * (t - s)))
      ≤ curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f) := by
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hf.1
  have hbma : (0 : ℝ) < b - a := by linarith
  have htms : (0 : ℝ) < t - s := by linarith
  have hfhomeo : IsHomeomorph f := hf.2.1
  set M := curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f) with hM
  set N := curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f) with hN
  -- `M ≤ K · (t−s)/(b−a)`: the crossing axis-rectangle bound.
  have hMK : M ≤ ENNReal.ofReal K * ENNReal.ofReal ((t - s) / (b - a)) :=
    hf.axisRect_le hab hst
  -- Reciprocity `1 ≤ M · N`.
  have hrecip : 1 ≤ M * N := conjugateImageModulus_reciprocity hfhomeo hab hst
  -- Chain: `1 ≤ M · N ≤ (K · (t−s)/(b−a)) · N`.
  have hchain : (1 : ℝ≥0∞) ≤ (ENNReal.ofReal K * ENNReal.ofReal ((t - s) / (b - a))) * N :=
    le_trans hrecip (by gcongr)
  -- The stated constant is the exact inverse of the bound on `M`.
  have hcancel : ENNReal.ofReal ((b - a) / (K * (t - s)))
      * (ENNReal.ofReal K * ENNReal.ofReal ((t - s) / (b - a))) = 1 := by
    have hK0 : K ≠ 0 := ne_of_gt hKpos
    have hb0 : b - a ≠ 0 := ne_of_gt hbma
    have ht0 : t - s ≠ 0 := ne_of_gt htms
    rw [← ENNReal.ofReal_mul hKpos.le,
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (b - a) / (K * (t - s)))]
    rw [show (b - a) / (K * (t - s)) * (K * ((t - s) / (b - a))) = 1 by field_simp]
    exact ENNReal.ofReal_one
  have hmul : ENNReal.ofReal ((b - a) / (K * (t - s))) * 1
      ≤ ENNReal.ofReal ((b - a) / (K * (t - s)))
        * ((ENNReal.ofReal K * ENNReal.ofReal ((t - s) / (b - a))) * N) := by gcongr
  have hrw : ENNReal.ofReal ((b - a) / (K * (t - s)))
      * ((ENNReal.ofReal K * ENNReal.ofReal ((t - s) / (b - a))) * N) = N := by
    rw [← mul_assoc, hcancel, one_mul]
  rwa [mul_one, hrw] at hmul

/-! ## The flat-density (Rengel) separation bound and the chord–area estimates -/

/-- **Flat-density separation bound for image curve families (Rengel's inequality).** If
every point of `f '' Q.leftSide` is at distance at least `d` from every point of
`f '' Q.rightSide`, then `d² · M(Q.imageCurveFamily f) ≤ area (f '' Q.image)`. Only
continuity of `f` is used.

*Proof sketch.* Membership in `Quadrilateral.imageCurveFamily` is by definition the tuple
(continuous, absolutely continuous on `[0,1]`, starts on `f '' leftSide`, ends on
`f '' rightSide`, stays in `f '' image`) — verbatim the curve hypothesis `hΓ` of the proved
`rengel_area_lower_bound`, discharged by `fun δ hδ => hδ`. Apply it with
`R := f '' Q.image` (compact by `Quadrilateral.isCompact_image` and continuity of `f`, hence
closed and measurable), `A₁ := f '' Q.leftSide`, `A₂ := f '' Q.rightSide`. The admissible
density behind that lemma is the flat `ρ = (1/d) · 𝟙_{f '' Q.image}`: an absolutely
continuous curve from `A₁` to `A₂` has arc length at least `dist(A₁, A₂) ≥ d`, and the
energy of `ρ` is `area/d²`.

This is Rengel's inequality in the honest form `s² ≤ M · m` with *side-set*
separation. -/
theorem imageCurveFamily_sep_sq_mul_modulus_le_volume {f : ℂ → ℂ} (hf : Continuous f)
    (Q : Quadrilateral) {d : ℝ} (hd : 0 < d)
    (hdist : ∀ p ∈ f '' Q.leftSide, ∀ q ∈ f '' Q.rightSide, d ≤ dist p q) :
    ENNReal.ofReal (d ^ 2) * curveModulus (Q.imageCurveFamily f)
      ≤ volume (f '' Q.image) := by
  have hRmeas : MeasurableSet (f '' Q.image) := (Q.isCompact_image.image hf).measurableSet
  exact rengel_area_lower_bound hRmeas hd hdist (fun δ hδ => hδ)

/-- **Chord–area estimate for an axis rectangle (horizontal/crossing form).** If the images
of the two vertical sides of `[a,b] × [s,t]` are separated by `d > 0`, then
`d² · (t−s)/(K·(b−a)) ≤ area (f '' ([a,b] × [s,t]))`, in real numbers.

*Proof sketch.* Chain the crossing-modulus lower bound `axisRect_imageModulus_ge` with the
flat-density separation bound `imageCurveFamily_sep_sq_mul_modulus_le_volume` (rewriting the
image region through `axisRectQuadrilateral_image`, which identifies `Q.image` with
`axisRect a b s t`): `ofReal (d²) · ofReal ((t−s)/(K(b−a))) ≤ ofReal (d²) · M ≤ volume`.
The image volume is finite (compact image), so the inequality transfers to `toReal` by
`ENNReal.toReal` monotonicity and `ENNReal.ofReal_mul`.
-/
theorem qc_sep_sq_le_imageArea_horizontal {f : ℂ → ℂ} {K : ℝ} (hf : AxisRectModulusBound f K)
    {a b s t d : ℝ} (hab : a < b) (hst : s < t) (hd : 0 < d)
    (hdist : ∀ p ∈ f '' (axisRectQuadrilateral a b s t hab hst).leftSide,
      ∀ q ∈ f '' (axisRectQuadrilateral a b s t hab hst).rightSide, d ≤ dist p q) :
    d ^ 2 * ((t - s) / (K * (b - a))) ≤ (volume (f '' axisRect a b s t)).toReal := by
  have hcont : Continuous f := hf.2.1.continuous
  have hmod := axisRect_imageModulus_ge hf hab hst
  have hrengel := imageCurveFamily_sep_sq_mul_modulus_le_volume hcont
    (axisRectQuadrilateral a b s t hab hst) hd hdist
  have himg : (axisRectQuadrilateral a b s t hab hst).image = axisRect a b s t :=
    axisRectQuadrilateral_image hab hst
  rw [himg] at hrengel
  have hchain : ENNReal.ofReal (d ^ 2) * ENNReal.ofReal ((t - s) / (K * (b - a)))
      ≤ volume (f '' axisRect a b s t) :=
    le_trans (by gcongr) hrengel
  have hfin : volume (f '' axisRect a b s t) ≠ ⊤ :=
    (((isCompact_axisRect a b s t).image hcont).measure_lt_top).ne
  rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ d ^ 2)] at hchain
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hchain

/-- **Chord–area estimate for an axis rectangle (vertical/separating form).** Mirror of
`qc_sep_sq_le_imageArea_horizontal`: if the images of the bottom and top sides of
`[a,b] × [s,t]` are separated by `d > 0`, then `d² · (b−a)/(K·(t−s)) ≤ area (f '' R)`.

*Proof sketch.* Same chain with the separating lower bound `axisRectSwap_imageModulus_ge`
and the swapped quadrilateral: `axisRectQuadrilateralSwap_leftSide`/`_rightSide` identify
its sides with the bottom edge `[a,b] × {s}` and top edge `[a,b] × {t}`, and
`axisRectQuadrilateralSwap_image` identifies its image region with the same rectangle. -/
theorem qc_sep_sq_le_imageArea_vertical {f : ℂ → ℂ} {K : ℝ} (hf : AxisRectModulusBound f K)
    {a b s t d : ℝ} (hab : a < b) (hst : s < t) (hd : 0 < d)
    (hdist : ∀ p ∈ f '' (axisRectQuadrilateralSwap a b s t hab hst).leftSide,
      ∀ q ∈ f '' (axisRectQuadrilateralSwap a b s t hab hst).rightSide, d ≤ dist p q) :
    d ^ 2 * ((b - a) / (K * (t - s))) ≤ (volume (f '' axisRect a b s t)).toReal := by
  have hcont : Continuous f := hf.2.1.continuous
  have hmod := axisRectSwap_imageModulus_ge hf hab hst
  have hrengel := imageCurveFamily_sep_sq_mul_modulus_le_volume hcont
    (axisRectQuadrilateralSwap a b s t hab hst) hd hdist
  have himg : (axisRectQuadrilateralSwap a b s t hab hst).image = axisRect a b s t := by
    rw [axisRectQuadrilateralSwap_image hab hst]
    exact axisRectQuadrilateral_image hab hst
  rw [himg] at hrengel
  have hchain : ENNReal.ofReal (d ^ 2) * ENNReal.ofReal ((b - a) / (K * (t - s)))
      ≤ volume (f '' axisRect a b s t) :=
    le_trans (by gcongr) hrengel
  have hfin : volume (f '' axisRect a b s t) ≠ ⊤ :=
    (((isCompact_axisRect a b s t).image hcont).measure_lt_top).ne
  rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ d ^ 2)] at hchain
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hchain

/-- **Thin-strip increment bound (horizontal slices).** For the strip `[c,d] × [y, y+h]`
whose vertical-edge images are pointwise `D`-separated — `D ≤ dist (f ⟨c,τ₁⟩) (f ⟨d,τ₂⟩)`
for all `τ₁, τ₂ ∈ [y, y+h]` — the image area dominates `D² · h/(K·(d−c))`.

*Proof sketch.* By `axisRectQuadrilateral_leftSide`/`_rightSide` the sides of the crossing
quadrilateral of `[c,d] × [y,y+h]` are exactly `{⟨c,τ⟩ : τ ∈ [y,y+h]}` and
`{⟨d,τ⟩ : τ ∈ [y,y+h]}`, so the hypothesis is precisely the side-set separation of
`qc_sep_sq_le_imageArea_horizontal` at `(c, d, y, y+h)`, whose aspect ratio is `h/(d−c)`.

As `h → 0⁺` the vertical edges of the strip degenerate to the two endpoints `⟨c,y⟩`,
`⟨d,y⟩` of a horizontal slice interval, so by continuity the side-set separation converges
to the specific slice increment `dist (f ⟨c,y⟩) (f ⟨d,y⟩)` — this is how the classical
proofs convert Rengel's side-set bound into a per-interval increment bound (Bishop,
Theorem 4.1: "any curve joining the opposite vertical sides limits on the bottom edge"). -/
theorem AxisRectModulusBound.horizontal_strip_sep_sq_le {f : ℂ → ℂ} {K : ℝ}
    (hf : AxisRectModulusBound f K) {c d y h D : ℝ} (hcd : c < d) (hh : 0 < h) (hD : 0 < D)
    (hsep : ∀ τ₁ ∈ Set.Icc y (y + h), ∀ τ₂ ∈ Set.Icc y (y + h),
      D ≤ dist (f ⟨c, τ₁⟩) (f ⟨d, τ₂⟩)) :
    D ^ 2 * (h / (K * (d - c))) ≤ (volume (f '' axisRect c d y (y + h))).toReal := by
  have hst' : y < y + h := by linarith
  have hdist' : ∀ p ∈ f '' (axisRectQuadrilateral c d y (y + h) hcd hst').leftSide,
      ∀ q ∈ f '' (axisRectQuadrilateral c d y (y + h) hcd hst').rightSide, D ≤ dist p q := by
    rintro p ⟨z, hz, rfl⟩ q ⟨w, hw, rfl⟩
    rw [axisRectQuadrilateral_leftSide hcd hst'] at hz
    rw [axisRectQuadrilateral_rightSide hcd hst'] at hw
    obtain ⟨hzre, hzim⟩ := hz
    obtain ⟨hwre, hwim⟩ := hw
    have hz' : z = (⟨c, z.im⟩ : ℂ) := Complex.ext hzre rfl
    have hw' : w = (⟨d, w.im⟩ : ℂ) := Complex.ext hwre rfl
    rw [hz', hw']
    exact hsep z.im (Set.mem_Icc.mpr hzim) w.im (Set.mem_Icc.mpr hwim)
  have hres := qc_sep_sq_le_imageArea_horizontal hf hcd hst' hD hdist'
  rw [show y + h - y = h by ring] at hres
  exact hres

/-- **Thin-strip increment bound (vertical slices).** Mirror of
`AxisRectModulusBound.horizontal_strip_sep_sq_le` for the strip `[x, x+h] × [c,d]` whose
horizontal-edge images are pointwise `D`-separated: the image area dominates
`D² · h/(K·(d−c))`.

*Proof sketch.* Instantiate `qc_sep_sq_le_imageArea_vertical` at `(x, x+h, c, d)` — the
separating lower bound contributes `(x+h−x)/(K·(d−c)) = h/(K·(d−c))` — after converting the
hypothesis through `axisRectQuadrilateralSwap_leftSide`/`_rightSide` (the bottom edge
`[x,x+h] × {c}` and top edge `[x,x+h] × {d}` consist exactly of the points `⟨τ₁,c⟩`,
`⟨τ₂,d⟩` with `τ₁, τ₂ ∈ [x, x+h]`). -/
theorem AxisRectModulusBound.vertical_strip_sep_sq_le {f : ℂ → ℂ} {K : ℝ}
    (hf : AxisRectModulusBound f K) {c d x h D : ℝ} (hcd : c < d) (hh : 0 < h) (hD : 0 < D)
    (hsep : ∀ τ₁ ∈ Set.Icc x (x + h), ∀ τ₂ ∈ Set.Icc x (x + h),
      D ≤ dist (f ⟨τ₁, c⟩) (f ⟨τ₂, d⟩)) :
    D ^ 2 * (h / (K * (d - c))) ≤ (volume (f '' axisRect x (x + h) c d)).toReal := by
  have hab' : x < x + h := by linarith
  have hdist' : ∀ p ∈ f '' (axisRectQuadrilateralSwap x (x + h) c d hab' hcd).leftSide,
      ∀ q ∈ f '' (axisRectQuadrilateralSwap x (x + h) c d hab' hcd).rightSide, D ≤ dist p q := by
    rintro p ⟨z, hz, rfl⟩ q ⟨w, hw, rfl⟩
    rw [axisRectQuadrilateralSwap_leftSide hab' hcd] at hz
    rw [axisRectQuadrilateralSwap_rightSide hab' hcd] at hw
    obtain ⟨hzim, hzre⟩ := hz
    obtain ⟨hwim, hwre⟩ := hw
    have hz' : z = (⟨z.re, c⟩ : ℂ) := Complex.ext rfl hzim
    have hw' : w = (⟨w.re, d⟩ : ℂ) := Complex.ext rfl hwim
    rw [hz', hw']
    exact hsep z.re (Set.mem_Icc.mpr hzre) w.re (Set.mem_Icc.mpr hwre)
  have hres := qc_sep_sq_le_imageArea_vertical hf hab' hcd hD hdist'
  rw [show x + h - x = h by ring] at hres
  exact hres

/-! ## The monotone image-area profiles

The classical monotone area function `A(y) = area (f '' ([α,β] × [σ,y]))` (the base
measure `Φ(A) = m(f(A × J))` of the length–area method). For
continuous `f` every value is finite (compact image), the profile is monotone, hence
differentiable a.e. by Lebesgue's theorem, and its derivative controls the per-height
Rengel sums. -/

/-- **Horizontal image-area profile**: `imageAreaProfileY f α β σ v` is the area of
`f '' ([α,β] × [σ,v])`, as a real number. Monotone in `v` for continuous `f`
(`monotone_imageAreaProfileY`); for `v < σ` the rectangle is empty and the profile
vanishes. -/
noncomputable def imageAreaProfileY (f : ℂ → ℂ) (α β σ : ℝ) : ℝ → ℝ :=
  fun v => (volume (f '' axisRect α β σ v)).toReal

/-- **Vertical image-area profile**: `imageAreaProfileX f α σ τ v` is the area of
`f '' ([α,v] × [σ,τ])`, as a real number. Monotone in `v` for continuous `f`
(`monotone_imageAreaProfileX`). -/
noncomputable def imageAreaProfileX (f : ℂ → ℂ) (α σ τ : ℝ) : ℝ → ℝ :=
  fun v => (volume (f '' axisRect α v σ τ)).toReal

/-- **Monotonicity of the horizontal image-area profile.** For `u ≤ v` the rectangle
`[α,β] × [σ,u]` is contained in `[α,β] × [σ,v]`, so the image volumes are ordered
(`measure_mono`); `ENNReal.toReal` preserves the order because the larger volume is finite
(continuous image of a compact rectangle, `isCompact_axisRect`). -/
theorem monotone_imageAreaProfileY {f : ℂ → ℂ} (hf : Continuous f) (α β σ : ℝ) :
    Monotone (imageAreaProfileY f α β σ) := by
  intro u v huv
  have hsub : axisRect α β σ u ⊆ axisRect α β σ v := by
    intro z hz
    simp only [axisRect, Set.mem_ofPred_eq] at hz ⊢
    exact ⟨hz.1, hz.2.1, le_trans hz.2.2 huv⟩
  exact ENNReal.toReal_mono (((isCompact_axisRect α β σ v).image hf).measure_lt_top).ne
    (measure_mono (Set.image_mono hsub))

/-- **Monotonicity of the vertical image-area profile.** Mirror of
`monotone_imageAreaProfileY`. -/
theorem monotone_imageAreaProfileX {f : ℂ → ℂ} (hf : Continuous f) (α σ τ : ℝ) :
    Monotone (imageAreaProfileX f α σ τ) := by
  intro u v huv
  have hsub : axisRect α u σ τ ⊆ axisRect α v σ τ := by
    intro z hz
    simp only [axisRect, Set.mem_ofPred_eq] at hz ⊢
    exact ⟨⟨hz.1.1, le_trans hz.1.2 huv⟩, hz.2⟩
  exact ENNReal.toReal_mono (((isCompact_axisRect α v σ τ).image hf).measure_lt_top).ne
    (measure_mono (Set.image_mono hsub))

/-- **Two-sided strip bound for the horizontal profile.** For an injective continuous `f`,
the image area of the strip `[α,β] × [y, y+δ]` is at most the profile increment across
`[y−δ, y+δ]`.

*Proof sketch.* The strip `[α,β] × [y, y+δ]` and the lower rectangle `[α,β] × [σ, y−δ]` are
disjoint (`im ≤ y−δ < y ≤ im` is impossible), and their union is contained in
`[α,β] × [σ, y+δ]`. Injectivity makes the two images disjoint; both are compact
(`isCompact_axisRect`, continuity), hence measurable with finite volume. Additivity of the
measure on the disjoint union, monotonicity into the big rectangle, and `toReal` arithmetic
with finiteness give the bound. -/
theorem imageArea_strip_le_profileY_diff {f : ℂ → ℂ} (hf : Continuous f)
    (hinj : Function.Injective f) {α β σ y δ : ℝ} (hδ : 0 < δ) (hσ : σ ≤ y - δ) :
    (volume (f '' axisRect α β y (y + δ))).toReal
      ≤ imageAreaProfileY f α β σ (y + δ) - imageAreaProfileY f α β σ (y - δ) := by
  -- The strip and the lower rectangle are disjoint …
  have hAB : Disjoint (axisRect α β y (y + δ)) (axisRect α β σ (y - δ)) := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    simp only [axisRect, Set.mem_ofPred_eq] at hzA hzB
    linarith [hzA.2.1, hzB.2.2]
  -- … and their union is contained in the big rectangle.
  have hsub : axisRect α β y (y + δ) ∪ axisRect α β σ (y - δ) ⊆ axisRect α β σ (y + δ) := by
    rintro z (hz | hz) <;> simp only [axisRect, Set.mem_ofPred_eq] at hz ⊢
    · exact ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
    · exact ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
  -- Compactness gives measurability and finite volume for all three images.
  have hcA : IsCompact (f '' axisRect α β y (y + δ)) := (isCompact_axisRect _ _ _ _).image hf
  have hcB : IsCompact (f '' axisRect α β σ (y - δ)) := (isCompact_axisRect _ _ _ _).image hf
  have hcC : IsCompact (f '' axisRect α β σ (y + δ)) := (isCompact_axisRect _ _ _ _).image hf
  have hdisj : Disjoint (f '' axisRect α β y (y + δ)) (f '' axisRect α β σ (y - δ)) :=
    Set.disjoint_image_of_injective hinj hAB
  -- Additivity on the disjoint union, monotonicity into the big rectangle.
  have hunion : volume (f '' axisRect α β y (y + δ)) + volume (f '' axisRect α β σ (y - δ))
      ≤ volume (f '' axisRect α β σ (y + δ)) := by
    calc volume (f '' axisRect α β y (y + δ)) + volume (f '' axisRect α β σ (y - δ))
        = volume (f '' axisRect α β y (y + δ) ∪ f '' axisRect α β σ (y - δ)) :=
          (measure_union hdisj hcB.measurableSet).symm
      _ = volume (f '' (axisRect α β y (y + δ) ∪ axisRect α β σ (y - δ))) := by
          rw [Set.image_union]
      _ ≤ volume (f '' axisRect α β σ (y + δ)) := measure_mono (Set.image_mono hsub)
  have h1 : (volume (f '' axisRect α β y (y + δ))).toReal
      + (volume (f '' axisRect α β σ (y - δ))).toReal
      ≤ (volume (f '' axisRect α β σ (y + δ))).toReal := by
    rw [← ENNReal.toReal_add hcA.measure_lt_top.ne hcB.measure_lt_top.ne]
    exact ENNReal.toReal_mono hcC.measure_lt_top.ne hunion
  simp only [imageAreaProfileY]
  linarith [h1]

/-- **Two-sided strip bound for the vertical profile.** Mirror of
`imageArea_strip_le_profileY_diff` for vertical strips `[x, x+δ] × [σ,τ]`. -/
theorem imageArea_strip_le_profileX_diff {f : ℂ → ℂ} (hf : Continuous f)
    (hinj : Function.Injective f) {α σ τ x δ : ℝ} (hδ : 0 < δ) (hα : α ≤ x - δ) :
    (volume (f '' axisRect x (x + δ) σ τ)).toReal
      ≤ imageAreaProfileX f α σ τ (x + δ) - imageAreaProfileX f α σ τ (x - δ) := by
  -- The strip and the left rectangle are disjoint …
  have hAB : Disjoint (axisRect x (x + δ) σ τ) (axisRect α (x - δ) σ τ) := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    simp only [axisRect, Set.mem_ofPred_eq] at hzA hzB
    linarith [hzA.1.1, hzB.1.2]
  -- … and their union is contained in the big rectangle.
  have hsub : axisRect x (x + δ) σ τ ∪ axisRect α (x - δ) σ τ ⊆ axisRect α (x + δ) σ τ := by
    rintro z (hz | hz) <;> simp only [axisRect, Set.mem_ofPred_eq] at hz ⊢
    · exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, hz.2⟩
    · exact ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩
  -- Compactness gives measurability and finite volume for all three images.
  have hcA : IsCompact (f '' axisRect x (x + δ) σ τ) := (isCompact_axisRect _ _ _ _).image hf
  have hcB : IsCompact (f '' axisRect α (x - δ) σ τ) := (isCompact_axisRect _ _ _ _).image hf
  have hcC : IsCompact (f '' axisRect α (x + δ) σ τ) := (isCompact_axisRect _ _ _ _).image hf
  have hdisj : Disjoint (f '' axisRect x (x + δ) σ τ) (f '' axisRect α (x - δ) σ τ) :=
    Set.disjoint_image_of_injective hinj hAB
  -- Additivity on the disjoint union, monotonicity into the big rectangle.
  have hunion : volume (f '' axisRect x (x + δ) σ τ) + volume (f '' axisRect α (x - δ) σ τ)
      ≤ volume (f '' axisRect α (x + δ) σ τ) := by
    calc volume (f '' axisRect x (x + δ) σ τ) + volume (f '' axisRect α (x - δ) σ τ)
        = volume (f '' axisRect x (x + δ) σ τ ∪ f '' axisRect α (x - δ) σ τ) :=
          (measure_union hdisj hcB.measurableSet).symm
      _ = volume (f '' (axisRect x (x + δ) σ τ ∪ axisRect α (x - δ) σ τ)) := by
          rw [Set.image_union]
      _ ≤ volume (f '' axisRect α (x + δ) σ τ) := measure_mono (Set.image_mono hsub)
  have h1 : (volume (f '' axisRect x (x + δ) σ τ)).toReal
      + (volume (f '' axisRect α (x - δ) σ τ)).toReal
      ≤ (volume (f '' axisRect α (x + δ) σ τ)).toReal := by
    rw [← ENNReal.toReal_add hcA.measure_lt_top.ne hcB.measure_lt_top.ne]
    exact ENNReal.toReal_mono hcC.measure_lt_top.ne hunion
  simp only [imageAreaProfileX]
  linarith [h1]

/-- **One-sided strip bound for the horizontal profile at a height with null segment
image.** If the horizontal segment `[α,β] × {y}` has null image, the image area of the
strip `[α,β] × [y, y+h]` is dominated by the one-sided profile increment
`Φ(y+h) − Φ(y)`.

*Proof sketch.* By injectivity, a strip point whose image also lies in
`f '' ([α,β] × [σ,y])` must lie on the shared segment `[α,β] × {y}`; hence
`f '' ([α,β] × [y,y+h]) ⊆ (f '' ([α,β] × [σ,y+h]) \ f '' ([α,β] × [σ,y])) ∪
f '' ([α,β] × {y})`. The segment image is null by hypothesis, so `measure_union_le` and
`measure_sdiff` (all sets compact, hence measurable and of finite volume) give the bound
after `toReal` arithmetic.

This is the step that lets the classical proofs compare a family of disjoint strips at
height `y` against the one-sided difference quotient `(A(y+h) − A(y))/h`. -/
theorem imageArea_strip_le_profileY_diff_right {f : ℂ → ℂ} (hf : Continuous f)
    (hinj : Function.Injective f) {α β σ y h : ℝ} (hh : 0 < h) (hσ : σ ≤ y)
    (hseg : volume (f '' axisRect α β y y) = 0) :
    (volume (f '' axisRect α β y (y + h))).toReal
      ≤ imageAreaProfileY f α β σ (y + h) - imageAreaProfileY f α β σ y := by
  have hcS : IsCompact (f '' axisRect α β y (y + h)) := (isCompact_axisRect _ _ _ _).image hf
  have hcL : IsCompact (f '' axisRect α β σ y) := (isCompact_axisRect _ _ _ _).image hf
  have hcC : IsCompact (f '' axisRect α β σ (y + h)) := (isCompact_axisRect _ _ _ _).image hf
  -- By injectivity, the strip image is covered by (big \ lower) ∪ segment image.
  have hsubset : f '' axisRect α β y (y + h)
      ⊆ (f '' axisRect α β σ (y + h) \ f '' axisRect α β σ y) ∪ f '' axisRect α β y y := by
    rintro w ⟨z, hzS, rfl⟩
    simp only [axisRect, Set.mem_ofPred_eq] at hzS
    by_cases hwL : f z ∈ f '' axisRect α β σ y
    · right
      obtain ⟨z', hz'L, hz'eq⟩ := hwL
      have hzz' : z' = z := hinj hz'eq
      rw [hzz'] at hz'L
      simp only [axisRect, Set.mem_ofPred_eq] at hz'L
      exact ⟨z, ⟨hzS.1, hzS.2.1, hz'L.2.2⟩, rfl⟩
    · left
      refine ⟨⟨z, ?_, rfl⟩, hwL⟩
      simp only [axisRect, Set.mem_ofPred_eq]
      exact ⟨hzS.1, by linarith [hzS.2.1], hzS.2.2⟩
  have hLC : f '' axisRect α β σ y ⊆ f '' axisRect α β σ (y + h) := by
    apply Set.image_mono
    intro z hz
    simp only [axisRect, Set.mem_ofPred_eq] at hz ⊢
    exact ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
  -- The segment image is null, so the strip image is dominated by the measure difference.
  have hle : volume (f '' axisRect α β y (y + h))
      ≤ volume (f '' axisRect α β σ (y + h)) - volume (f '' axisRect α β σ y) := by
    calc volume (f '' axisRect α β y (y + h))
        ≤ volume ((f '' axisRect α β σ (y + h) \ f '' axisRect α β σ y)
            ∪ f '' axisRect α β y y) := measure_mono hsubset
      _ ≤ volume (f '' axisRect α β σ (y + h) \ f '' axisRect α β σ y)
            + volume (f '' axisRect α β y y) := measure_union_le _ _
      _ = volume (f '' axisRect α β σ (y + h) \ f '' axisRect α β σ y) := by
          rw [hseg, add_zero]
      _ = volume (f '' axisRect α β σ (y + h)) - volume (f '' axisRect α β σ y) :=
          measure_sdiff hLC hcL.measurableSet.nullMeasurableSet hcL.measure_lt_top.ne
  have hvLC : volume (f '' axisRect α β σ y) ≤ volume (f '' axisRect α β σ (y + h)) :=
    measure_mono hLC
  have h2 := ENNReal.toReal_mono
    (ne_top_of_le_ne_top hcC.measure_lt_top.ne tsub_le_self) hle
  rw [ENNReal.toReal_sub_of_le hvLC hcC.measure_lt_top.ne] at h2
  simp only [imageAreaProfileY]
  exact h2

/-- **One-sided strip bound for the vertical profile at an abscissa with null segment
image.** Mirror of `imageArea_strip_le_profileY_diff_right` for vertical strips
`[x, x+h] × [σ,τ]` and the vertical segment `{x} × [σ,τ]`. -/
theorem imageArea_strip_le_profileX_diff_right {f : ℂ → ℂ} (hf : Continuous f)
    (hinj : Function.Injective f) {α σ τ x h : ℝ} (hh : 0 < h) (hα : α ≤ x)
    (hseg : volume (f '' axisRect x x σ τ) = 0) :
    (volume (f '' axisRect x (x + h) σ τ)).toReal
      ≤ imageAreaProfileX f α σ τ (x + h) - imageAreaProfileX f α σ τ x := by
  have hcS : IsCompact (f '' axisRect x (x + h) σ τ) := (isCompact_axisRect _ _ _ _).image hf
  have hcL : IsCompact (f '' axisRect α x σ τ) := (isCompact_axisRect _ _ _ _).image hf
  have hcC : IsCompact (f '' axisRect α (x + h) σ τ) := (isCompact_axisRect _ _ _ _).image hf
  -- By injectivity, the strip image is covered by (big \ left) ∪ segment image.
  have hsubset : f '' axisRect x (x + h) σ τ
      ⊆ (f '' axisRect α (x + h) σ τ \ f '' axisRect α x σ τ) ∪ f '' axisRect x x σ τ := by
    rintro w ⟨z, hzS, rfl⟩
    simp only [axisRect, Set.mem_ofPred_eq] at hzS
    by_cases hwL : f z ∈ f '' axisRect α x σ τ
    · right
      obtain ⟨z', hz'L, hz'eq⟩ := hwL
      have hzz' : z' = z := hinj hz'eq
      rw [hzz'] at hz'L
      simp only [axisRect, Set.mem_ofPred_eq] at hz'L
      exact ⟨z, ⟨⟨hzS.1.1, hz'L.1.2⟩, hzS.2⟩, rfl⟩
    · left
      refine ⟨⟨z, ?_, rfl⟩, hwL⟩
      simp only [axisRect, Set.mem_ofPred_eq]
      exact ⟨⟨by linarith [hzS.1.1], hzS.1.2⟩, hzS.2⟩
  have hLC : f '' axisRect α x σ τ ⊆ f '' axisRect α (x + h) σ τ := by
    apply Set.image_mono
    intro z hz
    simp only [axisRect, Set.mem_ofPred_eq] at hz ⊢
    exact ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩
  -- The segment image is null, so the strip image is dominated by the measure difference.
  have hle : volume (f '' axisRect x (x + h) σ τ)
      ≤ volume (f '' axisRect α (x + h) σ τ) - volume (f '' axisRect α x σ τ) := by
    calc volume (f '' axisRect x (x + h) σ τ)
        ≤ volume ((f '' axisRect α (x + h) σ τ \ f '' axisRect α x σ τ)
            ∪ f '' axisRect x x σ τ) := measure_mono hsubset
      _ ≤ volume (f '' axisRect α (x + h) σ τ \ f '' axisRect α x σ τ)
            + volume (f '' axisRect x x σ τ) := measure_union_le _ _
      _ = volume (f '' axisRect α (x + h) σ τ \ f '' axisRect α x σ τ) := by
          rw [hseg, add_zero]
      _ = volume (f '' axisRect α (x + h) σ τ) - volume (f '' axisRect α x σ τ) :=
          measure_sdiff hLC hcL.measurableSet.nullMeasurableSet hcL.measure_lt_top.ne
  have hvLC : volume (f '' axisRect α x σ τ) ≤ volume (f '' axisRect α (x + h) σ τ) :=
    measure_mono hLC
  have h2 := ENNReal.toReal_mono
    (ne_top_of_le_ne_top hcC.measure_lt_top.ne tsub_le_self) hle
  rw [ENNReal.toReal_sub_of_le hvLC hcC.measure_lt_top.ne] at h2
  simp only [imageAreaProfileX]
  exact h2

/-- **Derivative mass of a monotone real function.** For monotone `Φ : ℝ → ℝ` and
`s ≤ t`: `∫⁻ y in [s,t], ofReal (deriv Φ y) ≤ ofReal (Φ t − Φ s)`; in particular the
left-hand side is finite. (General-purpose one-dimensional fact; no quasiconformal input.)

*Proof sketch.* By Lebesgue's theorem (`Monotone.ae_hasDerivAt_deriv`), `Φ` has
`HasDerivAt Φ (deriv Φ y) y` at a.e. `y` (the junk value of `deriv` elsewhere is irrelevant
under the integral). Pointwise `ENNReal.ofReal (deriv Φ y) ≤ (‖deriv Φ y‖₊ : ℝ≥0∞)`, so
`lintegral_nnnorm_deriv_le_eVariationOn` bounds the integral by
`eVariationOn Φ (Icc s t)`, and `MonotoneOn.eVariationOn_eq` (with the universal set)
bounds the variation of the monotone `Φ` by `ofReal (Φ t − Φ s)`. -/
theorem lintegral_ofReal_deriv_le_of_monotone {Φ : ℝ → ℝ} (hΦ : Monotone Φ) {s t : ℝ}
    (hst : s ≤ t) :
    ∫⁻ y in Set.Icc s t, ENNReal.ofReal (deriv Φ y) ≤ ENNReal.ofReal (Φ t - Φ s) := by
  -- Lebesgue differentiation: `Φ` has a genuine derivative equal to `deriv Φ` a.e.
  have hderiv : ∀ᵐ y : ℝ, HasDerivAt Φ (deriv Φ y) y := by
    filter_upwards [hΦ.ae_hasDerivAt] with y hy using hy.differentiableAt.hasDerivAt
  -- Pointwise `ofReal (deriv Φ y) ≤ ‖deriv Φ y‖₊`.
  have h1 : ∫⁻ y in Set.Icc s t, ENNReal.ofReal (deriv Φ y)
      ≤ ∫⁻ y in Set.Icc s t, (‖deriv Φ y‖₊ : ℝ≥0∞) := by
    refine lintegral_mono fun y => ?_
    rw [← enorm_eq_nnnorm]
    exact Real.ofReal_le_enorm _
  -- The variation lower bound, then the monotone variation formula.
  have h2 : ∫⁻ y in Set.Icc s t, (‖deriv Φ y‖₊ : ℝ≥0∞) ≤ eVariationOn Φ (Set.Icc s t) :=
    lintegral_nnnorm_deriv_le_eVariationOn hst hderiv
  have h3 : eVariationOn Φ (Set.Icc s t) ≤ ENNReal.ofReal (Φ t - Φ s) := by
    have := ((hΦ.monotoneOn Set.univ).eVariationOn_eq (Set.mem_univ s) (Set.mem_univ t)).le
    rwa [Set.univ_inter] at this
  exact le_trans h1 (le_trans h2 h3)

/-- **Lebesgue differentiation of a monotone function, packaged for `deriv`.** A monotone
real function has, at almost every point, a genuine derivative equal to `deriv Φ y`, and
that derivative is nonnegative.

*Proof sketch.* `Monotone.ae_hasDerivAt` produces `HasDerivAt Φ ((rnDeriv μ_Φ volume y).toReal) y`
a.e., whose value is nonnegative by construction; `HasDerivAt.deriv` identifies it with
`deriv Φ y`. -/
theorem _root_.Monotone.ae_hasDerivAt_deriv {Φ : ℝ → ℝ} (hΦ : Monotone Φ) :
    ∀ᵐ y : ℝ, HasDerivAt Φ (deriv Φ y) y ∧ 0 ≤ deriv Φ y := by
  filter_upwards [hΦ.ae_hasDerivAt] with y hy
  refine ⟨hy.differentiableAt.hasDerivAt, ?_⟩
  rw [hy.deriv]
  exact ENNReal.toReal_nonneg

/-! ## Countably many segments with non-null image -/

/-- **Only countably many horizontal segments have non-null image.** For an injective
continuous `f`, the set of heights `y` whose segment `[α,β] × {y}` has image of positive
area is countable.

*Proof sketch.* The images `f '' ([α,β] × {y})`, `y : ℝ`, are pairwise disjoint
(injectivity of `f`, disjointness of the segments) and compact (`isCompact_axisRect` with
`s = t = y`, continuity), hence measurable. In the σ-finite Lebesgue measure on `ℂ`, among
pairwise disjoint measurable sets only countably many can have positive measure
(`MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion`); rewrite `≠ 0` as `0 <`. -/
theorem countable_pos_volume_image_horizontalSeg {f : ℂ → ℂ} (hf : Continuous f)
    (hinj : Function.Injective f) (α β : ℝ) :
    {y : ℝ | volume (f '' axisRect α β y y) ≠ 0}.Countable := by
  have hmble : ∀ y : ℝ, MeasurableSet (f '' axisRect α β y y) := fun y =>
    ((isCompact_axisRect α β y y).image hf).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint fun y : ℝ => f '' axisRect α β y y) := by
    intro y y' hne
    simp only [Function.onFun]
    have hd : Disjoint (axisRect α β y y) (axisRect α β y' y') := by
      rw [Set.disjoint_left]
      intro z hz hz'
      simp only [axisRect, Set.mem_ofPred_eq] at hz hz'
      exact hne (by linarith [hz.2.1, hz.2.2, hz'.2.1, hz'.2.2])
    exact Set.disjoint_image_of_injective hinj hd
  have hset : {y : ℝ | volume (f '' axisRect α β y y) ≠ 0}
      = {y : ℝ | 0 < volume (f '' axisRect α β y y)} := by
    ext y
    simp [pos_iff_ne_zero]
  rw [hset]
  exact MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion hmble hdisj

/-- **Only countably many vertical segments have non-null image.** Mirror of
`countable_pos_volume_image_horizontalSeg` for the vertical segments `{x} × [σ,τ]`. -/
theorem countable_pos_volume_image_verticalSeg {f : ℂ → ℂ} (hf : Continuous f)
    (hinj : Function.Injective f) (σ τ : ℝ) :
    {x : ℝ | volume (f '' axisRect x x σ τ) ≠ 0}.Countable := by
  have hmble : ∀ x : ℝ, MeasurableSet (f '' axisRect x x σ τ) := fun x =>
    ((isCompact_axisRect x x σ τ).image hf).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint fun x : ℝ => f '' axisRect x x σ τ) := by
    intro x x' hne
    simp only [Function.onFun]
    have hd : Disjoint (axisRect x x σ τ) (axisRect x' x' σ τ) := by
      rw [Set.disjoint_left]
      intro z hz hz'
      simp only [axisRect, Set.mem_ofPred_eq] at hz hz'
      exact hne (by linarith [hz.1.1, hz.1.2, hz'.1.1, hz'.1.2])
    exact Set.disjoint_image_of_injective hinj hd
  have hset : {x : ℝ | volume (f '' axisRect x x σ τ) ≠ 0}
      = {x : ℝ | 0 < volume (f '' axisRect x x σ τ)} := by
    ext x
    simp [pos_iff_ne_zero]
  rw [hset]
  exact MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion hmble hdisj

end NoWanderingDomains
