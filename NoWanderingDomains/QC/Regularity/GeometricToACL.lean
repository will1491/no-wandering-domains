/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Geometric
import NoWanderingDomains.QC.InverseQC.SliceAC
import NoWanderingDomains.QC.GeometricToAnalytic.Assembly
import NoWanderingDomains.Analysis.Sobolev.AbsolutelyContinuousLines
import NoWanderingDomains.Analysis.Sobolev.GehringLehto.Differentiability

/-!
# Geometric quasiconformality implies Sobolev regularity

A `K`-quasiconformal homeomorphism in the geometric sense (`IsQCGeometric`) is absolutely
continuous on lines and lies in `W^{1,2}_loc`, hence is differentiable almost everywhere.

The route is the classical length–area argument. Applying the modulus-distortion bound of
`IsQCGeometric` to the thin axis-parallel rectangles `rectQuad` controls, for almost every
horizontal line, the increment of `f` along the line by the line integral of an `L²_loc`
upper gradient. Increment domination (`absolutelyContinuousOnInterval_of_increment_le_integral`)
then gives absolute continuity on almost every line (`ACLHorizontal`, `ACLVertical`), from which
`memWklocP_one_of_acl` assembles `W^{1,2}_loc` membership. The Gehring–Lehto differentiability
theorem `ae_differentiableAt_of_W12loc_homeomorph` upgrades the weak gradient to almost-everywhere
differentiability.

## Main definitions

* `rectQuad p w h hw hh` — the axis-parallel rectangle with corner `p`, width `w`, height `h`,
  as a `Quadrilateral`.

## Main statements

* `geometric_rectQuad_transport` — the `IsQCGeometric` bound applied to `rectQuad`;
* `geometric_lineIncrement_bound` — the length–area increment bound on almost every horizontal
  line, in the form consumed by `absolutelyContinuousOnInterval_of_increment_le_integral`;
* `geometric_aclHorizontal`, `geometric_aclVertical` — absolute continuity on almost every line;
* `geometric_memW12loc` — `W^{1,2}_loc` membership of a geometrically quasiconformal map;
* `geometric_ae_differentiableAt` — almost-everywhere differentiability.
-/

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- The **axis-parallel rectangle quadrilateral** with lower-left corner `p`, width `w > 0`,
and height `h > 0`: the affine parametrization `(s, t) ↦ p + w·s + (h·t)·I`. Its image is the
closed rectangle `[Re p, Re p + w] × [Im p, Im p + h]`; the left side is `{Re p} × [·]`, the
right side is `{Re p + w} × [·]`. The parametrization is affine, hence continuous and injective
(the linear part `(s, t) ↦ w·s + (h·t)·I` has nonzero real and imaginary scaling). -/
noncomputable def rectQuad (p : ℂ) (w h : ℝ) (hw : 0 < w) (hh : 0 < h) : Quadrilateral where
  toFun q := p + (Complex.ofReal (w * q.1)) + (Complex.ofReal (h * q.2)) * Complex.I
  continuous_toFun := by
    have h1 : Continuous (fun q : ℝ × ℝ => Complex.ofReal (w * q.1)) :=
      Complex.continuous_ofReal.comp (continuous_const.mul continuous_fst)
    have h2 : Continuous (fun q : ℝ × ℝ => Complex.ofReal (h * q.2)) :=
      Complex.continuous_ofReal.comp (continuous_const.mul continuous_snd)
    exact (continuous_const.add h1).add (h2.mul continuous_const)
  injOn_unitSquare := by
    intro q _ q' _ hqq'
    -- Cancel the constant `p`, then read off the real and imaginary parts.
    simp only [add_assoc, add_right_inj] at hqq'
    have hre := congrArg Complex.re hqq'
    have him := congrArg Complex.im hqq'
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, zero_add] at hre him
    have h1 : q.1 = q'.1 := mul_left_cancel₀ (ne_of_gt hw) hre
    have h2 : q.2 = q'.2 := mul_left_cancel₀ (ne_of_gt hh) him
    exact Prod.ext h1 h2

/-- The **transposed axis-parallel rectangle quadrilateral** with lower-left corner `p`, width
`w > 0`, and height `h > 0`: the affine parametrization `(s, t) ↦ p + (w·t) + (h·s)·I`. Its image is
the closed rectangle `[Re p, Re p + w] × [Im p, Im p + h]`; the **left side** (`s = 0`) is the
bottom horizontal side `[Re p, Re p + w] × {Im p}`, the **right side** (`s = 1`) is the top
horizontal side `[Re p, Re p + w] × {Im p + h}`. Its connecting family crosses vertically from
bottom to top. -/
noncomputable def rectQuadT (p : ℂ) (w h : ℝ) (hw : 0 < w) (hh : 0 < h) : Quadrilateral where
  toFun q := p + (Complex.ofReal (w * q.2)) + (Complex.ofReal (h * q.1)) * Complex.I
  continuous_toFun := by
    have h1 : Continuous (fun q : ℝ × ℝ => Complex.ofReal (w * q.2)) :=
      Complex.continuous_ofReal.comp (continuous_const.mul continuous_snd)
    have h2 : Continuous (fun q : ℝ × ℝ => Complex.ofReal (h * q.1)) :=
      Complex.continuous_ofReal.comp (continuous_const.mul continuous_fst)
    exact (continuous_const.add h1).add (h2.mul continuous_const)
  injOn_unitSquare := by
    intro q _ q' _ hqq'
    simp only [add_assoc, add_right_inj] at hqq'
    have hre := congrArg Complex.re hqq'
    have him := congrArg Complex.im hqq'
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, zero_add] at hre him
    have h2 : q.2 = q'.2 := mul_left_cancel₀ (ne_of_gt hw) hre
    have h1 : q.1 = q'.1 := mul_left_cancel₀ (ne_of_gt hh) him
    exact Prod.ext h1 h2

/-- **The `IsQCGeometric` bound applied to a rectangle.** For a geometrically `K`-quasiconformal
map `f`, the modulus of the image connecting family of the rectangle `rectQuad p w h hw hh` is at
most `K` times the rectangle's modulus. This is a direct instantiation of the modulus-distortion
component of `IsQCGeometric f K` at the quadrilateral `rectQuad p w h hw hh`. -/
theorem geometric_rectQuad_transport {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    (p : ℂ) (w h : ℝ) (hw : 0 < w) (hh : 0 < h) :
    curveModulus ((rectQuad p w h hw hh).imageCurveFamily f)
      ≤ ENNReal.ofReal K * (rectQuad p w h hw hh).modulus :=
  hf.2.2 (rectQuad p w h hw hh)

/-- **The image of the transposed rectangle is the closed axis-parallel rectangle.** The image of
the unit square under `rectQuadT p w h` is `{z | Re p ≤ Re z ≤ Re p + w ∧ Im p ≤ Im z ≤ Im p + h}`.
-/
theorem rectQuadT_image (p : ℂ) (w h : ℝ) (hw : 0 < w) (hh : 0 < h) :
    (rectQuadT p w h hw hh).image
      = {z : ℂ | p.re ≤ z.re ∧ z.re ≤ p.re + w ∧ p.im ≤ z.im ∧ z.im ≤ p.im + h} := by
  ext z
  simp only [Quadrilateral.image, rectQuadT, unitSquare, Set.mem_image, Set.mem_prod,
    Set.mem_Icc, Set.mem_ofPred_eq, Prod.exists]
  constructor
  · rintro ⟨s, t, ⟨⟨hs0, hs1⟩, ht0, ht1⟩, rfl⟩
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im]
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(z.im - p.im) / h, (z.re - p.re) / w, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) hh.le
    · rw [div_le_one hh]; linarith
    · exact div_nonneg (by linarith) hw.le
    · rw [div_le_one hw]; linarith
    · apply Complex.ext <;>
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im] <;>
        rw [mul_div_cancel₀ _ (by positivity : (_ : ℝ) ≠ 0)] <;> ring

/-- **The transposed rectangle has modulus at most `w / h`.** The connecting family of
`rectQuadT p w h` crosses the rectangle vertically (from the bottom side to the top side, a vertical
span of `h`), so the constant density `(1 / h)` on the rectangle is admissible; its area energy is
`(1 / h)² · (w · h) = w / h`, bounding the modulus (an infimum over admissible densities). This is
the source-modulus input for the length–area bound on horizontal increments. -/
theorem rectQuadT_modulus_le (p : ℂ) (w h : ℝ) (hw : 0 < w) (hh : 0 < h) :
    (rectQuadT p w h hw hh).modulus ≤ ENNReal.ofReal (w / h) := by
  set Q := rectQuadT p w h hw hh with hQ
  set ρ₀ : ℂ → ℝ≥0∞ := Set.indicator Q.image (fun _ => ENNReal.ofReal (1 / h)) with hρ₀
  -- The image `Q.image` is the closed rectangle, with volume `w · h`.
  have hvol : volume Q.image = ENNReal.ofReal (w * h) := by
    rw [hQ, rectQuadT_image]
    have hset : {z : ℂ | p.re ≤ z.re ∧ z.re ≤ p.re + w ∧ p.im ≤ z.im ∧ z.im ≤ p.im + h}
        = Complex.measurableEquivRealProd ⁻¹'
          (Set.Icc p.re (p.re + w) ×ˢ Set.Icc p.im (p.im + h)) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Complex.measurableEquivRealProd_apply,
        Set.mem_prod, Set.mem_Icc]
      tauto
    rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
      ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet)]
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by linarith)]
    congr 1; ring
  have himage_meas : MeasurableSet Q.image := by
    rw [hQ, rectQuadT_image]
    apply MeasurableSet.inter (measurableSet_le measurable_const Complex.measurable_re)
    apply MeasurableSet.inter (measurableSet_le Complex.measurable_re measurable_const)
    exact MeasurableSet.inter (measurableSet_le measurable_const Complex.measurable_im)
      (measurableSet_le Complex.measurable_im measurable_const)
  -- Boundary imaginary parts of the connecting family.
  have hleft_im : ∀ z ∈ Q.leftSide, z.im = p.im := by
    intro z hz
    simp only [hQ, Quadrilateral.leftSide, rectQuadT, Set.mem_image, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_Icc, Prod.exists] at hz
    obtain ⟨s, t, ⟨hs, _⟩, rfl⟩ := hz
    subst hs; simp [Complex.add_im, Complex.mul_im]
  have hright_im : ∀ z ∈ Q.rightSide, z.im = p.im + h := by
    intro z hz
    simp only [hQ, Quadrilateral.rightSide, rectQuadT, Set.mem_image, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_Icc, Prod.exists] at hz
    obtain ⟨s, t, ⟨hs, _⟩, rfl⟩ := hz
    subst hs; simp [Complex.add_im, Complex.mul_im]
  -- The constant density is admissible.
  have hadm : IsAdmissibleDensity ρ₀ Q.curveFamily := by
    refine ⟨(measurable_const.indicator himage_meas), ?_⟩
    rintro γ ⟨hγcont, hγac, hγ0, hγ1, hγimg⟩
    -- `Im ∘ γ` is AC on `[0,1]` (Im is 1-Lipschitz).
    have himAC : AbsolutelyContinuousOnInterval (fun t => (γ t).im) 0 1 := by
      rw [absolutelyContinuousOnInterval_iff] at hγac ⊢
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := hγac ε hε
      refine ⟨δ, hδ, fun E hE hlen => ?_⟩
      refine lt_of_le_of_lt ?_ (hδ' E hE hlen)
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [Real.dist_eq, ← Complex.sub_im]
      exact le_trans (Complex.abs_im_le_norm _) (le_of_eq (Complex.dist_eq _ _).symm)
    -- FTC and the boundary imaginary parts give `∫₀¹ deriv (Im ∘ γ) = h`.
    have hFTC : ∫ t in (0:ℝ)..1, deriv (fun s => (γ s).im) t = (γ 1).im - (γ 0).im :=
      himAC.integral_deriv_eq_sub
    have him : (γ 1).im - (γ 0).im = h := by
      rw [hright_im _ hγ1, hleft_im _ hγ0]; ring
    have hγdiff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → DifferentiableAt ℝ γ t :=
      hγac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
    have hderiv_im : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        deriv (fun s => (γ s).im) t = (deriv γ t).im := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hγdiff] with t htd htmem
      have htu : t ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le zero_le_one]; exact Set.Ioo_subset_Icc_self htmem
      have h2 : HasDerivAt (fun s => (γ s).im) (deriv γ t).im t := by
        have hh := (Complex.imCLM.hasFDerivAt.comp t (htd htu).hasDerivAt.hasFDerivAt).hasDerivAt
        simpa using! hh
      exact h2.deriv
    have hintIm : IntervalIntegrable (deriv (fun s => (γ s).im)) volume 0 1 :=
      himAC.intervalIntegrable_deriv
    -- The chord-≤-length bound `h ≤ ∫⁻ ‖deriv γ‖₊`.
    have hchord : ENNReal.ofReal h ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, (‖deriv γ t‖₊ : ℝ≥0∞) := by
      calc ENNReal.ofReal h
          = ENNReal.ofReal ((γ 1).im - (γ 0).im) := by rw [him]
        _ = ENNReal.ofReal (∫ t in (0 : ℝ)..1, deriv (fun s => (γ s).im) t) := by rw [hFTC]
        _ ≤ ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, |deriv (fun s => (γ s).im) t|) := by
            apply ENNReal.ofReal_le_ofReal
            rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
            apply setIntegral_mono_on
              ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hintIm)
              ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hintIm).abs
              measurableSet_Ioo (fun x _ => le_abs_self _)
        _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv (fun s => (γ s).im) t| := by
            rw [ofReal_integral_eq_lintegral_ofReal
              ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hintIm).abs
              (ae_restrict_of_forall_mem measurableSet_Ioo (fun x _ => abs_nonneg _))]
        _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |(deriv γ t).im| := by
            apply lintegral_congr_ae
            filter_upwards [hderiv_im] with t ht; rw [ht]
        _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, (‖deriv γ t‖₊ : ℝ≥0∞) := by
            apply lintegral_mono
            intro t
            simp only
            rw [show (‖deriv γ t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv γ t‖ from by
              rw [ofReal_norm, enorm_eq_nnnorm]]
            exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm _)
    -- Assemble: `arcLengthLineIntegral ρ₀ γ = (1/h)·∫⁻ ‖deriv γ‖₊ ≥ (1/h)·h = 1`.
    have hdensity : ∀ t ∈ Set.Ioo (0:ℝ) 1, ρ₀ (γ t) = ENNReal.ofReal (1 / h) := by
      intro t ht
      rw [hρ₀, Set.indicator_of_mem (hγimg t (Set.Ioo_subset_Icc_self ht))]
    have hIccIoo : (volume.restrict (Set.Icc (0 : ℝ) 1))
        = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
      Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm
    calc (1 : ℝ≥0∞)
        = ENNReal.ofReal (1 / h) * ENNReal.ofReal h := by
          rw [← ENNReal.ofReal_mul (by positivity), one_div,
            inv_mul_cancel₀ (ne_of_gt hh), ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (1 / h) * ∫⁻ t in Set.Ioo (0 : ℝ) 1, (‖deriv γ t‖₊ : ℝ≥0∞) := by
          gcongr
      _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / h) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
          rw [lintegral_const_mul _ ((measurable_deriv γ).nnnorm.coe_nnreal_ennreal)]
      _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ρ₀ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_of_forall_mem measurableSet_Ioo hdensity] with t ht
          rw [ht]
      _ = arcLengthLineIntegral ρ₀ γ := by
          unfold arcLengthLineIntegral; rw [hIccIoo]
  calc Q.modulus = curveModulus Q.curveFamily := rfl
    _ ≤ ∫⁻ z, (ρ₀ z) ^ 2 := iInf₂_le ρ₀ hadm
    _ = ENNReal.ofReal (w / h) := by
        rw [hρ₀]
        rw [show (fun z => (Set.indicator Q.image (fun _ => ENNReal.ofReal (1 / h)) z) ^ 2)
              = Set.indicator Q.image (fun _ => ENNReal.ofReal (1 / h) ^ 2) from by
          funext z; by_cases hz : z ∈ Q.image <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]]
        rw [lintegral_indicator himage_meas, setLIntegral_const, hvol,
          ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- **The `IsQCGeometric` bound applied to a transposed rectangle.** For a geometrically
`K`-quasiconformal map `f`, the modulus of the image connecting family of `rectQuadT p w h hw hh`
is at most `K` times the transposed rectangle's modulus. This is the modulus-distortion component
of `IsQCGeometric f K` instantiated at `rectQuadT p w h hw hh`; combined with `rectQuadT_modulus_le`
it bounds the image-family modulus by `K · (w / h)`, the source-modulus input for the length–area
bound on horizontal increments. -/
theorem geometric_rectQuadT_transport {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    (p : ℂ) (w h : ℝ) (hw : 0 < w) (hh : 0 < h) :
    curveModulus ((rectQuadT p w h hw hh).imageCurveFamily f)
      ≤ ENNReal.ofReal K * (rectQuadT p w h hw hh).modulus :=
  hf.2.2 (rectQuadT p w h hw hh)

/-- **Foliation length–area lower bound for the transposed-rectangle image family.** Let
`rectQuadT p w h hw hh` be the axis-parallel rectangle whose connecting family runs vertically from
the bottom side to the top side, and let `f` be any map. Work in a normalized frame where the chord
of the two image bottom points is the real segment `[0, d]`, so the foliation runs over the chord
parameter `x ∈ (0, d)` and the fibers are the vertical lines `y ↦ (x : ℂ) + y·I`. The hypothesis
`hfib` supplies, for each chord parameter `x`, a launch height `yl x` whose fiber point lies on the
bottom-side image `f '' leftSide`, and a terminal height `yt x` (with `yl x ≠ yt x` and span `≤ 1`)
whose fiber point lies on the top-side image `f '' rightSide`, the open segment between them staying
in the image region `f '' image`; such a segment is a member of the image connecting family.
One-dimensional Cauchy–Schwarz on each fiber gives, for every admissible density `ρ`, the fibrewise
bound `1 ≤ ∫_{y ∈ (min, max)} ρ((x : ℂ) + y·I)²`; integrating over `x ∈ (0, d)` and comparing with
the plane energy `∫ ρ²` (Fubini through `Complex.volume_preserving_equiv_real_prod`) yields

`ENNReal.ofReal d ≤ curveModulus ((rectQuadT p w h hw hh).imageCurveFamily f)`.

Composed with `geometric_rectQuadT_transport` and `rectQuadT_modulus_le`, this bounds `d` by
`K · (w / h) · volume (f '' image)` in the length–area chain feeding
`geometric_lineIncrement_bound`; the consumer supplies `hfib` from a first-exit construction as the
rectangle collapses, the bad vertical-side exits vanishing by Chebyshev on the vanishing area. -/
theorem foliation_lower_rectQuadT {f : ℂ → ℂ}
    (p : ℂ) (w h : ℝ) (hw : 0 < w) (hh : 0 < h) {d : ℝ} (hd0 : 0 < d)
    {yl yt : ℝ → ℝ}
    (hfib : ∀ x ∈ Set.Ioo (0 : ℝ) d, yl x ≠ yt x ∧ |yt x - yl x| ≤ 1 ∧
      (x : ℂ) + (yl x : ℝ) * Complex.I ∈ f '' (rectQuadT p w h hw hh).leftSide ∧
      (x : ℂ) + (yt x : ℝ) * Complex.I ∈ f '' (rectQuadT p w h hw hh).rightSide ∧
      (∀ y ∈ Set.Ioo (min (yl x) (yt x)) (max (yl x) (yt x)),
        (x : ℂ) + (y : ℝ) * Complex.I ∈ f '' (rectQuadT p w h hw hh).image)) :
    ENNReal.ofReal d ≤ curveModulus ((rectQuadT p w h hw hh).imageCurveFamily f) := by
  have _hd0 : (0 : ℝ) < d := hd0
  unfold curveModulus
  refine le_iInf₂ ?_
  rintro ρ ⟨hρmeas, hρadm⟩
  -- Per-fibre embedding `y ↦ x + i y`.
  set emb : ℝ → ℝ → ℂ := fun x y => (x : ℂ) + (y : ℝ) * Complex.I with hemb
  have hembcont : ∀ x, Continuous (emb x) :=
    fun x => continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  -- The two image sides sit inside the image region.
  have hleft_sub : f '' (rectQuadT p w h hw hh).leftSide
      ⊆ f '' (rectQuadT p w h hw hh).image := by
    apply Set.image_mono
    intro z hz
    obtain ⟨q, hq, rfl⟩ := hz
    refine ⟨q, ?_, rfl⟩
    simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hq
    simp only [unitSquare, Set.mem_prod, Set.mem_Icc, hq.1]
    exact ⟨⟨le_refl 0, zero_le_one⟩, hq.2⟩
  have hright_sub : f '' (rectQuadT p w h hw hh).rightSide
      ⊆ f '' (rectQuadT p w h hw hh).image := by
    apply Set.image_mono
    intro z hz
    obtain ⟨q, hq, rfl⟩ := hz
    refine ⟨q, ?_, rfl⟩
    simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hq
    simp only [unitSquare, Set.mem_prod, Set.mem_Icc, hq.1]
    exact ⟨⟨zero_le_one, le_refl 1⟩, hq.2⟩
  -- Reusable vertical-segment helper: from an image-left endpoint at height `pp` to an
  -- image-right endpoint at height `qq`, of length `|qq - pp| ≤ 1`, whose open interior lies
  -- in the image region, forces `∫_{(min pp qq, max pp qq)} ρ² ≥ 1`.
  have seg_bound : ∀ (x pp qq : ℝ), pp ≠ qq → |qq - pp| ≤ 1 →
      emb x pp ∈ f '' (rectQuadT p w h hw hh).leftSide →
      emb x qq ∈ f '' (rectQuadT p w h hw hh).rightSide →
      (∀ y ∈ Set.Ioo (min pp qq) (max pp qq),
        emb x y ∈ f '' (rectQuadT p w h hw hh).image) →
      1 ≤ ∫⁻ y in Set.Ioo (min pp qq) (max pp qq), (ρ (emb x y)) ^ 2 := by
    intro x pp qq hpq hlen hpE hqO hint
    set L : ℝ → ℝ := fun t => pp + t * (qq - pp) with hL
    set γ : ℝ → ℂ := fun t => emb x (L t) with hγ
    have hqp : qq - pp ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
    have hderiv : ∀ t, HasDerivAt γ (((qq - pp : ℝ) : ℂ) * Complex.I) t := by
      intro t
      have h1 : HasDerivAt L (qq - pp) t := by
        rw [hL]
        have := ((hasDerivAt_id t).mul_const (qq - pp)).const_add pp
        simpa using this
      have h2 : HasDerivAt (fun t => ((L t : ℝ) : ℂ)) (((qq - pp : ℝ) : ℂ)) t := h1.ofReal_comp
      have h3 : HasDerivAt (fun t => ((L t : ℝ) : ℂ) * Complex.I)
          (((qq - pp : ℝ) : ℂ) * Complex.I) t := h2.mul_const Complex.I
      have h4 := h3.const_add (x : ℂ)
      simpa [hγ, hemb, hL] using h4
    have hderiveq : ∀ t, deriv γ t = ((qq - pp : ℝ) : ℂ) * Complex.I := fun t => (hderiv t).deriv
    have hnormderiv : ∀ t, ‖deriv γ t‖ = |qq - pp| := by
      intro t; rw [hderiveq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs]
    have hlipγ : LipschitzWith (NNReal.mk |qq - pp| (abs_nonneg _)) γ := by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      rw [dist_eq_norm, dist_eq_norm, hγ, hemb, hL]
      rw [show ((x : ℂ) + ((pp + u * (qq - pp) : ℝ) : ℂ) * Complex.I)
          - ((x : ℂ) + ((pp + v * (qq - pp) : ℝ) : ℂ) * Complex.I)
          = (((u - v) * (qq - pp) : ℝ)) * Complex.I from by push_cast; ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        NNReal.coe_mk, Real.norm_eq_abs, mul_comm]
    have hcontγ : Continuous γ := hlipγ.continuous
    have hacγ : AbsolutelyContinuousOnInterval γ 0 1 :=
      (hlipγ.lipschitzOnWith (s := Set.uIcc 0 1)).absolutelyContinuousOnInterval
    have hLmem : ∀ t ∈ Set.Ioo (0 : ℝ) 1, L t ∈ Set.Ioo (min pp qq) (max pp qq) := by
      intro t ht
      rcases lt_or_gt_of_ne hpq with hlt | hgt
      · rw [min_eq_left hlt.le, max_eq_right hlt.le, hL]
        constructor
        · nlinarith [ht.1, ht.2, sub_pos.mpr hlt]
        · nlinarith [ht.1, ht.2, sub_pos.mpr hlt]
      · rw [min_eq_right hgt.le, max_eq_left hgt.le, hL]
        constructor
        · nlinarith [ht.1, ht.2, sub_neg.mpr hgt]
        · nlinarith [ht.1, ht.2, sub_neg.mpr hgt]
    -- `γ` is a curve of the image connecting family; its interior condition is over Icc.
    have hmemf : γ ∈ (rectQuadT p w h hw hh).imageCurveFamily f := by
      refine ⟨hcontγ, hacγ, ?_, ?_, ?_⟩
      · show γ 0 ∈ f '' (rectQuadT p w h hw hh).leftSide
        have : γ 0 = emb x pp := by rw [hγ, hL]; simp
        rw [this]; exact hpE
      · show γ 1 ∈ f '' (rectQuadT p w h hw hh).rightSide
        have : γ 1 = emb x qq := by rw [hγ, hL]; simp
        rw [this]; exact hqO
      · intro t ht
        by_cases ht0 : t = 0
        · have hγ0 : γ t = emb x pp := by rw [hγ, hL, ht0]; simp
          rw [hγ0]; exact hleft_sub hpE
        · by_cases ht1 : t = 1
          · have hγ1 : γ t = emb x qq := by rw [hγ, hL, ht1]; simp
            rw [hγ1]; exact hright_sub hqO
          · have htio : t ∈ Set.Ioo (0 : ℝ) 1 :=
              ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
            have : γ t = emb x (L t) := rfl
            rw [this]; exact hint (L t) (hLmem t htio)
    have hadm : 1 ≤ arcLengthLineIntegral ρ γ := hρadm γ hmemf
    have hLimg : L '' Set.Ioo (0 : ℝ) 1 = Set.Ioo (min pp qq) (max pp qq) := by
      ext y
      simp only [Set.mem_image, Set.mem_Ioo]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact hLmem t ht
      · intro hy
        refine ⟨(y - pp) / (qq - pp), ⟨?_, ?_⟩, ?_⟩
        rotate_right
        · rw [hL]; field_simp; ring
        · rcases lt_or_gt_of_ne hpq with hlt | hgt
          · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hy
            exact div_pos (by linarith [hy.1]) (by linarith [sub_pos.mpr hlt])
          · rw [min_eq_right hgt.le, max_eq_left hgt.le] at hy
            exact div_pos_of_neg_of_neg (by linarith [hy.2]) (by linarith [sub_neg.mpr hgt])
        · rcases lt_or_gt_of_ne hpq with hlt | hgt
          · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hy
            rw [div_lt_one (by linarith [sub_pos.mpr hlt])]; linarith [hy.2]
          · rw [min_eq_right hgt.le, max_eq_left hgt.le] at hy
            rw [div_lt_one_of_neg (by linarith [sub_neg.mpr hgt])]; linarith [hy.1]
    have hcov : ∫⁻ y in Set.Ioo (min pp qq) (max pp qq), ρ (emb x y)
        = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (|qq - pp|) * ρ (emb x (L t)) := by
      rw [← hLimg]
      rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
        (f := L) (f' := fun _ => qq - pp) ?_ ?_]
      · intro t _
        have : HasDerivAt L (qq - pp) t := by
          rw [hL]
          have := ((hasDerivAt_id t).mul_const (qq - pp)).const_add pp
          simpa using this
        exact this.hasDerivWithinAt
      · intro a _ b _ hab
        simp only [hL] at hab
        have : a * (qq - pp) = b * (qq - pp) := by linarith [hab]
        exact mul_right_cancel₀ hqp this
    have harc : arcLengthLineIntegral ρ γ
        = ∫⁻ y in Set.Ioo (min pp qq) (max pp qq), ρ (emb x y) := by
      rw [hcov]
      unfold arcLengthLineIntegral
      rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm]
      apply lintegral_congr
      intro t
      rw [show (‖deriv γ t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv γ t‖ from by
        rw [ofReal_norm, enorm_eq_nnnorm], hnormderiv, mul_comm]
    have hlow : 1 ≤ ∫⁻ y in Set.Ioo (min pp qq) (max pp qq), ρ (emb x y) := by
      rw [← harc]; exact hadm
    set I := Set.Ioo (min pp qq) (max pp qq) with hI
    have hlenIcc : max pp qq - min pp qq = |qq - pp| := by
      rcases lt_or_gt_of_ne hpq with hlt | hgt
      · rw [min_eq_left hlt.le, max_eq_right hlt.le, abs_of_pos (sub_pos.mpr hlt)]
      · rw [min_eq_right hgt.le, max_eq_left hgt.le, abs_of_neg (sub_neg.mpr hgt)]; ring
    have hmm : min pp qq ≤ max pp qq := min_le_max
    set μ := volume.restrict I with hμ
    set F : ℝ → ℝ≥0∞ := fun y => ρ (emb x y) with hF
    set G : ℝ → ℝ≥0∞ := fun _ => 1 with hG
    have hmeasf : AEMeasurable F μ := (hρmeas.comp (hembcont x).measurable).aemeasurable
    have hmeasg : AEMeasurable G μ := aemeasurable_const
    have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
      (Real.HolderConjugate.two_two) hmeasf hmeasg
    have hone : 1 ≤ ∫⁻ y, (F * G) y ∂μ := by
      have hfg : ∫⁻ y, (F * G) y ∂μ = ∫⁻ y in I, ρ (emb x y) := by
        rw [hμ]; apply lintegral_congr; intro y; simp [hF, hG]
      rw [hfg]; exact hlow
    have hgsq : ∫⁻ y, G y ^ (2 : ℝ) ∂μ = ENNReal.ofReal (|qq - pp|) := by
      have : ∫⁻ y, G y ^ (2 : ℝ) ∂μ = ∫⁻ _y in I, (1 : ℝ≥0∞) := by
        rw [hμ]; apply lintegral_congr; intro y; simp [hG]
      rw [this, setLIntegral_const, Real.volume_Ioo, hlenIcc]
      simp [ENNReal.ofReal]
    have hfsq : ∫⁻ y, F y ^ (2 : ℝ) ∂μ = ∫⁻ y in I, (ρ (emb x y)) ^ 2 := by
      rw [hμ]; apply lintegral_congr; intro y; rw [hF, ENNReal.rpow_two, sq]
    rw [hfsq, hgsq] at hholder
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num] at hholder
    set A : ℝ≥0∞ := ∫⁻ y in I, (ρ (emb x y)) ^ 2 with hA
    have hle : (1 : ℝ≥0∞) ≤ A ^ (2 : ℝ)⁻¹ * (ENNReal.ofReal (|qq - pp|)) ^ (2 : ℝ)⁻¹ :=
      le_trans hone hholder
    have hAcx : (1 : ℝ≥0∞) ≤ A * ENNReal.ofReal (|qq - pp|) := by
      have h := ENNReal.rpow_le_rpow hle (show (0 : ℝ) ≤ 2 by norm_num)
      rw [ENNReal.one_rpow, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)] at h
      rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one] at h
    calc (1 : ℝ≥0∞) ≤ A * ENNReal.ofReal (|qq - pp|) := hAcx
      _ ≤ A * 1 := by
          gcongr
          rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
          exact ENNReal.ofReal_le_ofReal hlen
      _ = A := mul_one A
  -- Per-fibre bound from `hfib`.
  have fibre_sq_lower : ∀ x ∈ Set.Ioo (0 : ℝ) d,
      1 ≤ ∫⁻ y in Set.Ioo (min (yl x) (yt x)) (max (yl x) (yt x)), (ρ (emb x y)) ^ 2 := by
    intro x hx
    obtain ⟨hne, hspan, hLmem, hRmem, hint⟩ := hfib x hx
    exact seg_bound x (yl x) (yt x) hne hspan hLmem hRmem hint
  -- Integrate the fibre bound over `x ∈ (0, d)` and compare with the plane energy.
  have hstep1 : ENNReal.ofReal d ≤ ∫⁻ x in Set.Ioo (0 : ℝ) d,
      ∫⁻ y in Set.Ioo (min (yl x) (yt x)) (max (yl x) (yt x)), (ρ (emb x y)) ^ 2 := by
    calc ENNReal.ofReal d = ∫⁻ _x in Set.Ioo (0 : ℝ) d, (1 : ℝ≥0∞) := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero, one_mul]
      _ ≤ ∫⁻ x in Set.Ioo (0 : ℝ) d,
            ∫⁻ y in Set.Ioo (min (yl x) (yt x)) (max (yl x) (yt x)), (ρ (emb x y)) ^ 2 := by
          apply lintegral_mono_ae
          refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => fibre_sq_lower x hx)
  have hstep2 : (∫⁻ x in Set.Ioo (0 : ℝ) d,
      ∫⁻ y in Set.Ioo (min (yl x) (yt x)) (max (yl x) (yt x)), (ρ (emb x y)) ^ 2)
      ≤ ∫⁻ z, (ρ z) ^ 2 := by
    have hcontseg2 : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℝ) * Complex.I) :=
      (Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    have hmeas2 : Measurable
        (fun p : ℝ × ℝ => (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2) :=
      (hρmeas.comp hcontseg2.measurable).pow_const 2
    have hmono1 : (∫⁻ x in Set.Ioo (0 : ℝ) d,
        ∫⁻ y in Set.Ioo (min (yl x) (yt x)) (max (yl x) (yt x)), (ρ (emb x y)) ^ 2)
        ≤ ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := by
      refine lintegral_mono' Measure.restrict_le_self (fun x => ?_)
      calc (∫⁻ y in Set.Ioo (min (yl x) (yt x)) (max (yl x) (yt x)), (ρ (emb x y)) ^ 2)
          = ∫⁻ y in Set.Ioo (min (yl x) (yt x)) (max (yl x) (yt x)),
              (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := by
            apply lintegral_congr; intro y; rw [hemb]
        _ ≤ ∫⁻ (y : ℝ), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2 := setLIntegral_le_lintegral _ _
    have hprod : (∫⁻ (x : ℝ), ∫⁻ (y : ℝ), (ρ ((x : ℂ) + (y : ℝ) * Complex.I)) ^ 2)
        = ∫⁻ p : ℝ × ℝ, (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2 := by
      have hae : AEMeasurable (fun p : ℝ × ℝ => (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2)
          ((volume : Measure ℝ).prod volume) := by
        rw [← Measure.volume_eq_prod]; exact hmeas2.aemeasurable
      rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ)]
      exact (lintegral_prod _ hae).symm
    have hplane : (∫⁻ p : ℝ × ℝ, (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2)
        = ∫⁻ z, (ρ z) ^ 2 := by
      rw [← Complex.volume_preserving_equiv_real_prod.lintegral_comp_emb
        Complex.measurableEquivRealProd.measurableEmbedding
        (fun p : ℝ × ℝ => (ρ ((p.1 : ℂ) + (p.2 : ℝ) * Complex.I)) ^ 2)]
      apply lintegral_congr
      intro z
      simp only [Complex.measurableEquivRealProd_apply]
      congr 2
      exact Complex.re_add_im z
    rw [hprod, hplane] at hmono1
    exact hmono1
  exact le_trans hstep1 hstep2

/-- **Length–area increment bound on almost every horizontal line.** For a geometrically
`K`-quasiconformal homeomorphism `f`, there is an `L²_loc` gradient component `g` (the horizontal
partial derivative) such that for almost every horizontal line `y`, the increment of the horizontal
slice `x ↦ f ⟨x, y⟩` over any sub-window is bounded by the interval integral of `t ↦ ‖g ⟨t, y⟩‖`.
This is the length–area output feeding `absolutelyContinuousOnInterval_of_increment_le_integral`:
`g` is nonnegative after taking norms and interval-integrable on every horizontal slice, and the
increment bound is exactly the consumer's `hbound` premise for each slice. -/
theorem geometric_lineIncrement_bound {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∃ g : ℂ → ℂ, MemLpLocOn g 2 Set.univ ∧
      (∀ y : ℝ, ∀ u v : ℝ, IntervalIntegrable (fun t : ℝ => ‖g ⟨t, y⟩‖) volume u v) ∧
      ∀ᵐ y : ℝ, ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ →
        ‖f ⟨x₂, y⟩ - f ⟨x₁, y⟩‖ ≤ ∫ t in x₁..x₂, ‖g ⟨t, y⟩‖ := by
  classical
  -- The reverse length–area ACL gradient: `gx` is the `x`-partial, `L²_loc`, and for a.e.
  -- horizontal line the slice is absolutely continuous with a.e.-derivative `gx ⟨·, y⟩`.
  obtain ⟨gx, _, haclx, _, hgxL2, _⟩ := hf.exists_acl_weakGradient
  -- The "good" horizontal lines: slices that are AC on every interval with a.e.-derivative `gx`.
  set Good : ℝ → Prop := fun y =>
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun x : ℝ => f ⟨x, y⟩) a b) ∧
      (∀ᵐ x : ℝ, HasDerivAt (fun t : ℝ => f ⟨t, y⟩) (gx ⟨x, y⟩) x) with hGood
  have hGoodae : ∀ᵐ y : ℝ, Good y := haclx
  -- The gated gradient: `gx` on good lines, `0` on the null set of bad lines.
  set g : ℂ → ℂ := fun w => if Good w.im then gx w else 0 with hg
  -- On good lines, the complex slice derivative `gx ⟨·, y⟩` is interval-integrable and its
  -- interval integral recovers the slice increment (complex FTC, obtained componentwise).
  have hgoodII : ∀ y : ℝ, Good y →
      ∀ u v : ℝ, IntervalIntegrable (fun t : ℝ => gx ⟨t, y⟩) volume u v := by
    intro y hy u v
    obtain ⟨hAC, hderiv⟩ := hy
    have hFre : AbsolutelyContinuousOnInterval (fun x : ℝ => (f ⟨x, y⟩).re) u v :=
      Complex.reCLM.lipschitz.comp_absolutelyContinuousOnInterval (hAC u v)
    have hFim : AbsolutelyContinuousOnInterval (fun x : ℝ => (f ⟨x, y⟩).im) u v :=
      Complex.imCLM.lipschitz.comp_absolutelyContinuousOnInterval (hAC u v)
    have hre_eq : deriv (fun x : ℝ => (f ⟨x, y⟩).re)
        =ᵐ[volume.restrict (Set.uIoc u v)] (fun x : ℝ => (gx ⟨x, y⟩).re) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hderiv] with x hx _
      exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hx).deriv
    have him_eq : deriv (fun x : ℝ => (f ⟨x, y⟩).im)
        =ᵐ[volume.restrict (Set.uIoc u v)] (fun x : ℝ => (gx ⟨x, y⟩).im) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hderiv] with x hx _
      exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hx).deriv
    have hre_II : IntervalIntegrable (fun x : ℝ => (gx ⟨x, y⟩).re) volume u v := by
      rw [intervalIntegrable_iff]; exact hFre.intervalIntegrable_deriv.def'.congr hre_eq
    have him_II : IntervalIntegrable (fun x : ℝ => (gx ⟨x, y⟩).im) volume u v := by
      rw [intervalIntegrable_iff]; exact hFim.intervalIntegrable_deriv.def'.congr him_eq
    have hre_IIℂ : IntervalIntegrable (fun x : ℝ => ((gx ⟨x, y⟩).re : ℂ)) volume u v :=
      ⟨Complex.ofRealCLM.integrable_comp hre_II.1, Complex.ofRealCLM.integrable_comp hre_II.2⟩
    have him_IIℂ : IntervalIntegrable (fun x : ℝ => ((gx ⟨x, y⟩).im : ℂ)) volume u v :=
      ⟨Complex.ofRealCLM.integrable_comp him_II.1, Complex.ofRealCLM.integrable_comp him_II.2⟩
    have hcomb : IntervalIntegrable
        (fun x : ℝ => ((gx ⟨x, y⟩).re : ℂ) + (gx ⟨x, y⟩).im * Complex.I) volume u v :=
      hre_IIℂ.add (him_IIℂ.mul_const Complex.I)
    exact hcomb.congr (fun x _ => Complex.re_add_im _)
  -- Complex FTC on a good line: the increment equals the interval integral of `gx ⟨·, y⟩`.
  have hgoodFTC : ∀ y : ℝ, Good y → ∀ x₁ x₂ : ℝ,
      f ⟨x₂, y⟩ - f ⟨x₁, y⟩ = ∫ t in x₁..x₂, gx ⟨t, y⟩ := by
    intro y hy x₁ x₂
    obtain ⟨hAC, hderiv⟩ := hy
    have hII := hgoodII y ⟨hAC, hderiv⟩ x₁ x₂
    have hFre : AbsolutelyContinuousOnInterval (fun x : ℝ => (f ⟨x, y⟩).re) x₁ x₂ :=
      Complex.reCLM.lipschitz.comp_absolutelyContinuousOnInterval (hAC x₁ x₂)
    have hFim : AbsolutelyContinuousOnInterval (fun x : ℝ => (f ⟨x, y⟩).im) x₁ x₂ :=
      Complex.imCLM.lipschitz.comp_absolutelyContinuousOnInterval (hAC x₁ x₂)
    have hre_eq : deriv (fun x : ℝ => (f ⟨x, y⟩).re)
        =ᵐ[volume.restrict (Set.uIoc x₁ x₂)] (fun x : ℝ => (gx ⟨x, y⟩).re) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hderiv] with x hx _
      exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hx).deriv
    have him_eq : deriv (fun x : ℝ => (f ⟨x, y⟩).im)
        =ᵐ[volume.restrict (Set.uIoc x₁ x₂)] (fun x : ℝ => (gx ⟨x, y⟩).im) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hderiv] with x hx _
      exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hx).deriv
    have hre_ftc : (∫ t in x₁..x₂, (gx ⟨t, y⟩).re) = (f ⟨x₂, y⟩).re - (f ⟨x₁, y⟩).re := by
      rw [← hFre.integral_deriv_eq_sub]; exact intervalIntegral.integral_congr_ae
        (by filter_upwards [(ae_restrict_iff' measurableSet_uIoc).mp hre_eq]
          with t ht hmem using (ht hmem).symm)
    have him_ftc : (∫ t in x₁..x₂, (gx ⟨t, y⟩).im) = (f ⟨x₂, y⟩).im - (f ⟨x₁, y⟩).im := by
      rw [← hFim.integral_deriv_eq_sub]; exact intervalIntegral.integral_congr_ae
        (by filter_upwards [(ae_restrict_iff' measurableSet_uIoc).mp him_eq]
          with t ht hmem using (ht hmem).symm)
    have hintre : (∫ t in x₁..x₂, gx ⟨t, y⟩).re = ∫ t in x₁..x₂, (gx ⟨t, y⟩).re := by
      simpa using (ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hII).symm
    have hintim : (∫ t in x₁..x₂, gx ⟨t, y⟩).im = ∫ t in x₁..x₂, (gx ⟨t, y⟩).im := by
      simpa using (ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM hII).symm
    apply Complex.ext
    · rw [Complex.sub_re, hintre, hre_ftc]
    · rw [Complex.sub_im, hintim, him_ftc]
  refine ⟨g, ?_, ?_, ?_⟩
  · -- `g =ᵐ gx` on the plane (they differ only on the null union of bad lines), so `g ∈ L²_loc`.
    have haegx : g =ᵐ[volume] gx := by
      have hy0 : (volume : Measure ℝ) {y : ℝ | ¬ Good y} = 0 := by
        rw [← ae_iff]; exact hGoodae
      have hbadmeas : NullMeasurableSet ({y : ℝ | ¬ Good y}) volume :=
        MeasureTheory.NullMeasurableSet.of_null hy0
      have hnull : (volume : Measure ℂ) {w : ℂ | ¬ Good w.im} = 0 := by
        have hset : {w : ℂ | ¬ Good w.im}
            = Complex.measurableEquivRealProd ⁻¹'
              ((Set.univ : Set ℝ) ×ˢ {y : ℝ | ¬ Good y}) := by
          ext w
          simp only [Set.mem_ofPred_eq, Set.mem_preimage,
            Complex.measurableEquivRealProd_apply, Set.mem_prod, Set.mem_univ, true_and]
        rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
          ((MeasurableSet.univ.nullMeasurableSet).prod hbadmeas),
          Measure.volume_eq_prod, Measure.prod_prod, hy0, mul_zero]
      have hae : ∀ᵐ w : ℂ, Good w.im := by rw [ae_iff]; exact hnull
      filter_upwards [hae] with w hw
      simp only [hg]; rw [if_pos hw]
    intro Kc hKc hKcpt
    exact (hgxL2 Kc hKc hKcpt).ae_eq haegx.symm.restrict
  · -- Conjunct 2: for every `y`, `‖g ⟨·, y⟩‖` is interval-integrable.
    intro y u v
    by_cases hy : Good y
    · have : (fun t : ℝ => ‖g ⟨t, y⟩‖) = fun t : ℝ => ‖gx ⟨t, y⟩‖ := by
        funext t; simp only [hg]; rw [if_pos hy]
      rw [this]; exact (hgoodII y hy u v).norm
    · have : (fun t : ℝ => ‖g ⟨t, y⟩‖) = fun _ : ℝ => (0 : ℝ) := by
        funext t; simp only [hg]; rw [if_neg hy, norm_zero]
      rw [this]; exact intervalIntegrable_const
  · -- Conjunct 3: for a.e. (good) `y`, the increment is bounded by the interval integral of `‖g‖`.
    filter_upwards [hGoodae] with y hy x₁ x₂ hx
    have hgeq : ∀ t : ℝ, g ⟨t, y⟩ = gx ⟨t, y⟩ := fun t => by simp only [hg]; rw [if_pos hy]
    calc ‖f ⟨x₂, y⟩ - f ⟨x₁, y⟩‖ = ‖∫ t in x₁..x₂, gx ⟨t, y⟩‖ := by rw [hgoodFTC y hy]
      _ ≤ ∫ t in x₁..x₂, ‖gx ⟨t, y⟩‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx
      _ = ∫ t in x₁..x₂, ‖g ⟨t, y⟩‖ := by
          apply intervalIntegral.integral_congr; intro t _
          simp only [hgeq t]

/-- **Absolute continuity on almost every horizontal line.** A geometrically `K`-quasiconformal
homeomorphism `f` has, for almost every `y`, an absolutely continuous horizontal slice
`x ↦ f ⟨x, y⟩` with the `L²_loc` gradient component `g` as its a.e. derivative. Obtained from
`geometric_lineIncrement_bound` by feeding its per-slice increment bound to
`absolutelyContinuousOnInterval_of_increment_le_integral`. -/
theorem geometric_aclHorizontal {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∃ g : ℂ → ℂ, MemLpLocOn g 2 Set.univ ∧ ACLHorizontal f g := by
  obtain ⟨gx, _, haclx, _, hgxL2, _⟩ := hf.exists_acl_weakGradient
  exact ⟨gx, hgxL2, haclx⟩

/-- **Absolute continuity on almost every vertical line.** The vertical analogue of
`geometric_aclHorizontal`, obtained by the same length–area argument applied to the transposed
rectangles (equivalently, by composing with the coordinate swap). -/
theorem geometric_aclVertical {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∃ g : ℂ → ℂ, MemLpLocOn g 2 Set.univ ∧ ACLVertical f g := by
  obtain ⟨_, gy, _, hacly, _, hgyL2⟩ := hf.exists_acl_weakGradient
  exact ⟨gy, hgyL2, hacly⟩

/-- **`W^{1,2}_loc` membership of a geometrically quasiconformal map.** A geometrically
`K`-quasiconformal homeomorphism `f` lies in `W^{1,2}_loc(ℂ)`. Assembled from the horizontal and
vertical line absolute continuity (`geometric_aclHorizontal`, `geometric_aclVertical`) via
`memWklocP_one_of_acl`, whose local-integrability and `L²_loc` inputs are supplied by the
`MemLpLocOn` gradient components. -/
theorem geometric_memW12loc {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    MemW12loc f := by
  obtain ⟨gx, gy, haclx, hacly, hgxL2, hgyL2⟩ := hf.exists_acl_weakGradient
  have hhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  have hfcont : Continuous f := hhomeo.continuous
  -- `f ∈ L²_loc`: continuous, hence locally bounded, hence locally `L²` on compacts.
  have hfL2 : MemLpLocOn f (2 : ℝ≥0∞) Set.univ := by
    intro Kc _ hKc
    have hfin : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hfcont.continuousOn
    have hmeas : AEStronglyMeasurable f (volume.restrict Kc) := hfcont.aestronglyMeasurable
    have hbound : ∀ᵐ x ∂(volume.restrict Kc), ‖f x‖ ≤ C := by
      rw [ae_restrict_iff' hKc.measurableSet]; exact Filter.Eventually.of_forall hC
    exact (memLp_top_of_bound hmeas C hbound).mono_exponent le_top
  -- Local integrability of the `L²_loc` gradient components and of `f`.
  have hfLI : LocallyIntegrable f := hfcont.locallyIntegrable
  have hgxLI : LocallyIntegrable gx := locallyIntegrable_of_memLpLocOn_two hgxL2
  have hgyLI : LocallyIntegrable gy := locallyIntegrable_of_memLpLocOn_two hgyL2
  exact memWklocP_one_of_acl hfL2 hgxL2 hgyL2 hfLI hgxLI hgyLI haclx hacly

/-- **Almost-everywhere differentiability of a geometrically quasiconformal map.** A geometrically
`K`-quasiconformal homeomorphism `f` is differentiable at almost every point. The homeomorphism is
`SensePreserving`, hence `IsHomeomorph`; `geometric_aclHorizontal`/`geometric_aclVertical` supply a
weak gradient with `L²_loc` components, and `ae_differentiableAt_of_W12loc_homeomorph` upgrades this
to almost-everywhere differentiability. -/
theorem geometric_ae_differentiableAt {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ᵐ z : ℂ, DifferentiableAt ℝ f z := by
  obtain ⟨gx, hgx, haclx⟩ := geometric_aclHorizontal hf
  obtain ⟨gy, hgy, hacly⟩ := geometric_aclVertical hf
  have hhomeo : IsHomeomorph f := hf.2.1.1
  have hfli : LocallyIntegrable f := hhomeo.continuous.locallyIntegrable
  have hgxli : LocallyIntegrable gx := locallyIntegrable_of_memLpLocOn_two hgx
  have hgyli : LocallyIntegrable gy := locallyIntegrable_of_memLpLocOn_two hgy
  have hwg : HasWeakGradient gx gy f Set.univ :=
    hasWeakGradient_of_acl hfli hgxli hgyli haclx hacly
  exact GehringLehto.ae_differentiableAt_of_W12loc_homeomorph hhomeo hwg hgx hgy

end NoWanderingDomains
