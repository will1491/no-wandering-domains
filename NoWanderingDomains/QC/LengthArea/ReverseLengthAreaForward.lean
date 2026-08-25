/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Geometric
import NoWanderingDomains.QC.LengthArea.LengthAreaInverse

/-!
# The axis-aligned rectangle quadrilateral and the slice-energy length–area inequality

This file builds the foundational bricks for the **reverse length–area inequality**: the
**axis-aligned rectangle** `R = [a, b] × [s, t]`, realized as a `Quadrilateral`
(`axisRectQuadrilateral`), its exact conformal modulus
`modulus (axisRectQuadrilateral a b s t) = ENNReal.ofReal ((t − s) / (b − a))`, the
image-family modulus bound `M(f(R)) ≤ K · (t − s)/(b − a)` for a geometric
`K`-quasiconformal `f` (`axisRect_imageModulus_le`).

These are the axiom-clean foundational bricks of the reverse length–area method: the exact
rectangle modulus and its quasiconformal distortion bound.

## Main definitions

* `axisRectQuadrilateral a b s t hab hst` — the rectangle `[a, b] × [s, t]` as a
  `Quadrilateral`;
* `axisRect_modulus` — the modulus equals `ENNReal.ofReal ((t − s) / (b − a))`;
* `axisRect_imageModulus_le` — the image-family modulus distortion bound.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- The affine parametrization `⟨x, y⟩ ↦ ⟨a + (b−a)·x, s + (t−s)·y⟩` of the unit
square onto the rectangle `[a, b] × [s, t]`, viewed as a map `ℝ × ℝ → ℂ`. -/
noncomputable def axisRectMap (a b s t : ℝ) : ℝ × ℝ → ℂ :=
  fun p => Complex.mk (a + (b - a) * p.1) (s + (t - s) * p.2)

theorem axisRectMap_continuous (a b s t : ℝ) : Continuous (axisRectMap a b s t) := by
  unfold axisRectMap
  have h1 : Continuous (fun p : ℝ × ℝ => a + (b - a) * p.1) :=
    continuous_const.add (continuous_const.mul continuous_fst)
  have h2 : Continuous (fun p : ℝ × ℝ => s + (t - s) * p.2) :=
    continuous_const.add (continuous_const.mul continuous_snd)
  have : (fun p : ℝ × ℝ => Complex.mk (a + (b - a) * p.1) (s + (t - s) * p.2))
      = fun p : ℝ × ℝ =>
        ((a + (b - a) * p.1 : ℝ) : ℂ) + ((s + (t - s) * p.2 : ℝ) : ℝ) * Complex.I := by
    funext p; apply Complex.ext <;> simp
  rw [this]
  exact (Complex.continuous_ofReal.comp h1).add
    ((Complex.continuous_ofReal.comp h2).mul continuous_const)

theorem axisRectMap_injOn {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    Set.InjOn (axisRectMap a b s t) unitSquare := by
  intro p _ q _ h
  unfold axisRectMap at h
  have hre : a + (b - a) * p.1 = a + (b - a) * q.1 := congrArg Complex.re h
  have him : s + (t - s) * p.2 = s + (t - s) * q.2 := congrArg Complex.im h
  have h1 : p.1 = q.1 := by
    have := add_left_cancel hre
    exact mul_left_cancel₀ (ne_of_gt (by linarith : (0:ℝ) < b - a)) this
  have h2 : p.2 = q.2 := by
    have := add_left_cancel him
    exact mul_left_cancel₀ (ne_of_gt (by linarith : (0:ℝ) < t - s)) this
  exact Prod.ext h1 h2

/-- The **axis-aligned rectangle** `[a, b] × [s, t]` as a `Quadrilateral`, via the
affine parametrization `⟨x, y⟩ ↦ ⟨a + (b−a)·x, s + (t−s)·y⟩` of the unit square. -/
noncomputable def axisRectQuadrilateral (a b s t : ℝ) (hab : a < b) (hst : s < t) :
    Quadrilateral where
  toFun := axisRectMap a b s t
  continuous_toFun := axisRectMap_continuous a b s t
  injOn_unitSquare := axisRectMap_injOn hab hst

@[simp] theorem axisRectQuadrilateral_toFun (a b s t : ℝ) (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateral a b s t hab hst).toFun = axisRectMap a b s t := rfl

/-! ## Geometry of the rectangle: image, left and right sides -/

/-- The image of the rectangle quadrilateral is exactly the closed rectangle
`[a, b] × [s, t]`, identified with `{z : ℂ | a ≤ z.re ≤ b ∧ s ≤ z.im ≤ t}`. -/
theorem axisRectQuadrilateral_image {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateral a b s t hab hst).image
      = {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ (s ≤ z.im ∧ z.im ≤ t)} := by
  have hbma : (0:ℝ) < b - a := by linarith
  have htms : (0:ℝ) < t - s := by linarith
  ext z
  simp only [Quadrilateral.image, axisRectQuadrilateral_toFun, unitSquare, axisRectMap,
    Set.mem_image, Set.mem_prod, Set.mem_Icc, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨⟨hx0, hx1⟩, hy0, hy1⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [Complex.re, Complex.im] <;> nlinarith
  · rintro ⟨⟨hre0, hre1⟩, him0, him1⟩
    refine ⟨⟨(z.re - a)/(b - a), (z.im - s)/(t - s)⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) hbma.le
    · rw [div_le_one hbma]; linarith
    · exact div_nonneg (by linarith) htms.le
    · rw [div_le_one htms]; linarith
    · apply Complex.ext <;> dsimp only [Complex.re, Complex.im] <;>
        field_simp <;> ring

/-- The left side of the rectangle quadrilateral is the segment `{a} × [s, t]`. -/
theorem axisRectQuadrilateral_leftSide {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateral a b s t hab hst).leftSide
      = {z : ℂ | z.re = a ∧ (s ≤ z.im ∧ z.im ≤ t)} := by
  have htms : (0:ℝ) < t - s := by linarith
  ext z
  simp only [Quadrilateral.leftSide, axisRectQuadrilateral_toFun, axisRectMap,
    Set.mem_image, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨rfl, hy0, hy1⟩, rfl⟩
    refine ⟨by dsimp only [Complex.re]; ring, ?_, ?_⟩ <;>
      dsimp only [Complex.im] <;> nlinarith
  · rintro ⟨hre, him0, him1⟩
    refine ⟨⟨0, (z.im - s)/(t - s)⟩, ⟨rfl, ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) htms.le
    · rw [div_le_one htms]; linarith
    · apply Complex.ext <;> dsimp only [Complex.re, Complex.im]
      · rw [mul_zero, add_zero]; exact hre.symm
      · field_simp; ring

/-- The right side of the rectangle quadrilateral is the segment `{b} × [s, t]`. -/
theorem axisRectQuadrilateral_rightSide {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateral a b s t hab hst).rightSide
      = {z : ℂ | z.re = b ∧ (s ≤ z.im ∧ z.im ≤ t)} := by
  have htms : (0:ℝ) < t - s := by linarith
  ext z
  simp only [Quadrilateral.rightSide, axisRectQuadrilateral_toFun, axisRectMap,
    Set.mem_image, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨rfl, hy0, hy1⟩, rfl⟩
    refine ⟨by dsimp only [Complex.re]; ring, ?_, ?_⟩ <;>
      dsimp only [Complex.im] <;> nlinarith
  · rintro ⟨hre, him0, him1⟩
    refine ⟨⟨1, (z.im - s)/(t - s)⟩, ⟨rfl, ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) htms.le
    · rw [div_le_one htms]; linarith
    · apply Complex.ext <;> dsimp only [Complex.re, Complex.im]
      · rw [mul_one]; linarith [hre]
      · field_simp; ring

/-! ## The modulus lower bound -/

/-- The straight horizontal segments `x ↦ ⟨a + (b−a)·x, y⟩` (`y ∈ [s, t]`) form a
*subfamily* of the rectangle's connecting curve family. -/
theorem axisRect_segmentFamily_subset {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    {γ : ℝ → ℂ | ∃ y ∈ Set.Icc s t, γ = fun x : ℝ => Complex.mk (a + (b - a) * x) y}
      ⊆ (axisRectQuadrilateral a b s t hab hst).curveFamily := by
  rintro γ ⟨y, ⟨hys, hyt⟩, rfl⟩
  have hbma : (0:ℝ) < b - a := by linarith
  -- the segment is the affine image of the constant-`y` line; it is continuous and AC.
  have heq : (fun x : ℝ => Complex.mk (a + (b - a) * x) y)
      = fun x : ℝ => ((a + (b - a) * x : ℝ) : ℂ) + ((y : ℝ) : ℝ) * Complex.I := by
    funext x; apply Complex.ext <;> simp
  have hderiv : ∀ x, HasDerivAt (fun x : ℝ => Complex.mk (a + (b - a) * x) y)
      ((b - a : ℝ) : ℂ) x := by
    intro x
    rw [heq]
    have hr : HasDerivAt (fun x : ℝ => (a + (b - a) * x : ℝ)) (b - a) x := by
      have h1 : HasDerivAt (fun x : ℝ => (b - a) * x) (b - a) x := by
        simpa only [mul_one] using! (hasDerivAt_id x).const_mul (b - a)
      simpa only [zero_add] using! (hasDerivAt_const x a).add h1
    exact (hr.ofReal_comp).add_const ((y : ℝ) * Complex.I)
  have hcont : Continuous (fun x : ℝ => Complex.mk (a + (b - a) * x) y) := by
    rw [heq]
    refine (Complex.continuous_ofReal.comp ?_).add continuous_const
    exact continuous_const.add (continuous_const.mul continuous_id)
  -- The affine curve is globally Lipschitz with constant `b − a`.
  have hlip : LipschitzWith (Real.toNNReal (b - a))
      (fun x : ℝ => Complex.mk (a + (b - a) * x) y) := by
    rw [heq]
    refine LipschitzWith.of_dist_le_mul (fun x₁ x₂ => ?_)
    have hd : dist (((a + (b - a) * x₁ : ℝ) : ℂ) + ((y : ℝ) : ℝ) * Complex.I)
        (((a + (b - a) * x₂ : ℝ) : ℂ) + ((y : ℝ) : ℝ) * Complex.I)
        = |b - a| * dist x₁ x₂ := by
      rw [Complex.dist_eq]
      have hsub : (((a + (b - a) * x₁ : ℝ) : ℂ) + ((y : ℝ) : ℝ) * Complex.I)
          - (((a + (b - a) * x₂ : ℝ) : ℂ) + ((y : ℝ) : ℝ) * Complex.I)
          = (((b - a) * (x₁ - x₂) : ℝ) : ℂ) := by push_cast; ring
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq, abs_mul]
    rw [hd, Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ b - a),
      abs_of_pos hbma]
  refine ⟨hcont, ?_, ?_, ?_, ?_⟩
  · -- absolute continuity: a Lipschitz (in fact affine) curve is AC on every interval.
    exact (hlip.lipschitzOnWith).absolutelyContinuousOnInterval
  · -- `γ 0 ∈ leftSide`
    rw [axisRectQuadrilateral_leftSide]
    refine ⟨?_, ?_, ?_⟩ <;> dsimp only [Complex.re, Complex.im] <;>
      first | ring | linarith
  · -- `γ 1 ∈ rightSide`
    rw [axisRectQuadrilateral_rightSide]
    refine ⟨?_, ?_, ?_⟩ <;> dsimp only [Complex.re, Complex.im] <;>
      first | ring | linarith
  · -- stays in the image
    intro x hx
    rw [axisRectQuadrilateral_image]
    simp only [Set.mem_Icc] at hx
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [Complex.re, Complex.im] <;> nlinarith [hx.1, hx.2]

/-- **Modulus lower bound for the rectangle.** The rectangle's modulus is at least
`ENNReal.ofReal ((t − s)/(b − a))`. The straight horizontal segments crossing the
rectangle form a subfamily whose modulus is bounded below by the Cauchy–Schwarz /
Fubini length–area inequality `lengthArea_modulus_lower_bound`; modulus monotonicity
transfers this to the full family. -/
theorem axisRect_modulus_lower_bound {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    ENNReal.ofReal ((t - s) / (b - a))
      ≤ (axisRectQuadrilateral a b s t hab hst).modulus := by
  unfold Quadrilateral.modulus
  exact le_trans (lengthArea_modulus_lower_bound hab hst)
    (curveModulus_mono (axisRect_segmentFamily_subset hab hst))

/-! ## The modulus upper bound -/

/-- **Horizontal-increment ≤ arc length.** For an absolutely continuous curve
`γ : ℝ → ℂ` on `[0, 1]`, the increment of the real part `Re(γ 1) − Re(γ 0)` is at
most the total arc length `∫₀¹ ‖γ'‖`. This is the projection inequality
`|(γ')_re| ≤ ‖γ'‖` integrated through the fundamental theorem of calculus for the
absolutely continuous real part `Re ∘ γ`. -/
theorem reIncrement_le_arcLength {γ : ℝ → ℂ} (hγac : AbsolutelyContinuousOnInterval γ 0 1) :
    ENNReal.ofReal ((γ 1).re - (γ 0).re)
      ≤ ∫⁻ t in Set.Icc (0:ℝ) 1, (‖deriv γ t‖₊ : ℝ≥0∞) := by
  -- `g := Re ∘ γ` is absolutely continuous on `[0, 1]` (Lipschitz composition).
  set g : ℝ → ℝ := fun t => (γ t).re with hg_def
  have hg_ac : AbsolutelyContinuousOnInterval g 0 1 := by
    have hl : ∀ {F : ℝ → ℂ} {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (K : NNReal),
        LipschitzWith K l → ∀ {a c : ℝ}, AbsolutelyContinuousOnInterval F a c →
        AbsolutelyContinuousOnInterval (fun t => l (F t)) a c := by
      intro F Y _ l K hl a c hF
      rw [absolutelyContinuousOnInterval_iff] at hF ⊢
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
      refine ⟨δ, hδ, fun E hE hlen => ?_⟩
      have key := hδ' E hE hlen
      have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
      calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
          ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
            Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
        _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
            rw [Finset.mul_sum]
        _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
        _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
    exact hl Complex.reCLM ‖Complex.reCLM‖₊ Complex.reCLM.lipschitz hγac
  -- The real FTC for `g`: `∫₀¹ g' = g 1 − g 0`.
  have hg_int : IntervalIntegrable (deriv g) volume 0 1 := hg_ac.intervalIntegrable_deriv
  have hftc : ∫ t in (0:ℝ)..1, deriv g t = (γ 1).re - (γ 0).re := hg_ac.integral_deriv_eq_sub
  -- Convert the interval integral to an integral over `Ioc 0 1`.
  have hioc : ∫ t in (0:ℝ)..1, deriv g t = ∫ t in Set.Ioc (0:ℝ) 1, deriv g t :=
    intervalIntegral.integral_of_le (by norm_num)
  have hg_int' : IntegrableOn (deriv g) (Set.Ioc (0:ℝ) 1) volume := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hg_int
    exact hg_int
  -- `∫_{Ioc} g' ≤ ∫_{Ioc} |g'| = ∫_{Ioc} ‖g'‖`, and `ofReal (∫ ‖g'‖) = ∫⁻ ‖g'‖ₑ`.
  have hbound1 : ENNReal.ofReal ((γ 1).re - (γ 0).re)
      ≤ ∫⁻ t in Set.Ioc (0:ℝ) 1, (‖deriv g t‖₊ : ℝ≥0∞) := by
    rw [← hftc, hioc]
    calc ENNReal.ofReal (∫ t in Set.Ioc (0:ℝ) 1, deriv g t)
        ≤ ENNReal.ofReal (∫ t in Set.Ioc (0:ℝ) 1, ‖deriv g t‖) := by
          apply ENNReal.ofReal_le_ofReal
          refine integral_mono hg_int' hg_int'.norm (fun t => ?_)
          exact Real.le_norm_self _
      _ = ∫⁻ t in Set.Ioc (0:ℝ) 1, ‖deriv g t‖ₑ := by
          rw [ofReal_integral_norm_eq_lintegral_enorm hg_int']
      _ = ∫⁻ t in Set.Ioc (0:ℝ) 1, (‖deriv g t‖₊ : ℝ≥0∞) := by
          apply lintegral_congr; intro t; rw [enorm_eq_nnnorm]
  -- Pointwise `‖g' t‖ = |(γ' t).re| ≤ ‖γ' t‖` a.e. (where `γ` is differentiable).
  have hγ_diff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ γ t :=
    hγac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  have hbound2 : ∫⁻ t in Set.Ioc (0:ℝ) 1, (‖deriv g t‖₊ : ℝ≥0∞)
      ≤ ∫⁻ t in Set.Ioc (0:ℝ) 1, (‖deriv γ t‖₊ : ℝ≥0∞) := by
    apply lintegral_mono_ae
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hγ_diff] with t htdiff htmem
    have hd : DifferentiableAt ℝ γ t :=
      htdiff (Set.mem_uIcc.mpr (Or.inl (Set.Ioc_subset_Icc_self htmem)))
    -- `deriv g t = (deriv γ t).re`.
    have hderiv_g : deriv g t = (deriv γ t).re := by
      have hh : HasDerivAt g (deriv γ t).re t := by
        have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt
        simpa [hg_def] using! this
      exact hh.deriv
    rw [hderiv_g, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
      Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm (deriv γ t))
  -- Combine, then enlarge `Ioc 0 1` to `Icc 0 1`.
  refine hbound1.trans (hbound2.trans ?_)
  exact lintegral_mono_set Set.Ioc_subset_Icc_self

/-- The closed rectangle `[a, b] × [s, t]` as a subset of `ℂ`. -/
def axisRect (a b s t : ℝ) : Set ℂ :=
  {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ (s ≤ z.im ∧ z.im ≤ t)}

theorem measurableSet_axisRect (a b s t : ℝ) : MeasurableSet (axisRect a b s t) := by
  unfold axisRect
  apply MeasurableSet.inter
  · exact (measurableSet_le measurable_const Complex.measurable_re).inter
      (measurableSet_le Complex.measurable_re measurable_const)
  · exact (measurableSet_le measurable_const Complex.measurable_im).inter
      (measurableSet_le Complex.measurable_im measurable_const)

/-- The Lebesgue measure of the rectangle `[a, b] × [s, t] ⊆ ℂ` is
`ofReal (b − a) · ofReal (t − s)`. -/
theorem volume_axisRect (a b s t : ℝ) :
    volume (axisRect a b s t) = ENNReal.ofReal (b - a) * ENNReal.ofReal (t - s) := by
  have hpre : axisRect a b s t
      = Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc s t) := by
    ext z
    simp only [axisRect, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Icc,
      Complex.measurableEquivRealProd_apply]
  rw [hpre,
    Complex.volume_preserving_equiv_real_prod.measure_preimage
      ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet),
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]

/-- The extremal density for the rectangle: the constant `1/(b − a)` on the rectangle,
`0` elsewhere. -/
noncomputable def axisRectDensity (a b s t : ℝ) : ℂ → ℝ≥0∞ :=
  (axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (b - a)))

theorem measurable_axisRectDensity (a b s t : ℝ) : Measurable (axisRectDensity a b s t) :=
  Measurable.indicator measurable_const (measurableSet_axisRect a b s t)

/-- **Energy of the extremal density** equals `(t − s)/(b − a)`. -/
theorem lintegralSq_axisRectDensity {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    ∫⁻ z, (axisRectDensity a b s t z) ^ 2 = ENNReal.ofReal ((t - s) / (b - a)) := by
  have hbma : (0:ℝ) < b - a := by linarith
  have htms : (0:ℝ) < t - s := by linarith
  have hsq : (fun z => (axisRectDensity a b s t z) ^ 2)
      = (axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (b - a)) ^ 2) := by
    funext z
    unfold axisRectDensity
    by_cases hz : z ∈ axisRect a b s t <;> simp [hz]
  rw [hsq, lintegral_indicator (measurableSet_axisRect a b s t), setLIntegral_const,
    volume_axisRect a b s t]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [one_div]
  field_simp

/-- The extremal density is admissible for the rectangle's connecting curve family:
every absolutely continuous curve `γ` from the left side to the right side staying in
the rectangle has `∫_γ ρ ds ≥ 1`. -/
theorem axisRectDensity_admissible {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    IsAdmissibleDensity (axisRectDensity a b s t)
      (axisRectQuadrilateral a b s t hab hst).curveFamily := by
  have hbma : (0:ℝ) < b - a := by linarith
  refine ⟨measurable_axisRectDensity a b s t, ?_⟩
  rintro γ ⟨hγcont, hγac, hγ0, hγ1, hγimg⟩
  -- The endpoints are on the left/right sides: `Re(γ 0) = a`, `Re(γ 1) = b`.
  rw [axisRectQuadrilateral_leftSide] at hγ0
  rw [axisRectQuadrilateral_rightSide] at hγ1
  obtain ⟨hγ0re, _⟩ := hγ0
  obtain ⟨hγ1re, _⟩ := hγ1
  -- On `[0, 1]`, `γ t` is in the rectangle, so `ρ (γ t) = ofReal (1/(b−a))`.
  have hγimg' : ∀ u ∈ Set.Icc (0:ℝ) 1, γ u ∈ axisRect a b s t := by
    intro u hu
    have hmem := hγimg u hu
    rw [axisRectQuadrilateral_image] at hmem
    exact hmem
  have hργ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      axisRectDensity a b s t (γ u) = ENNReal.ofReal (1 / (b - a)) := by
    intro u hu
    unfold axisRectDensity
    rw [Set.indicator_of_mem (hγimg' u hu)]
  -- The arc-length line integral factors as `ofReal(1/(b−a)) · ∫⁻ ‖γ'‖`.
  have harc : arcLengthLineIntegral (axisRectDensity a b s t) γ
      = ENNReal.ofReal (1 / (b - a)) * ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv γ u‖₊ : ℝ≥0∞) := by
    unfold arcLengthLineIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    simp only
    rw [hργ u hu]
  rw [harc]
  -- The increment bound: `∫⁻ ‖γ'‖ ≥ ofReal(b−a)`, hence the product is `≥ 1`.
  have hincr : ENNReal.ofReal (b - a)
      ≤ ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv γ u‖₊ : ℝ≥0∞) := by
    have := reIncrement_le_arcLength hγac
    rwa [hγ1re, hγ0re] at this
  calc (1 : ℝ≥0∞)
      = ENNReal.ofReal (1 / (b - a)) * ENNReal.ofReal (b - a) := by
        rw [← ENNReal.ofReal_mul (by positivity), one_div,
          inv_mul_cancel₀ (by linarith : (b - a) ≠ 0), ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (1 / (b - a)) * ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv γ u‖₊ : ℝ≥0∞) := by
        gcongr

/-- **Modulus upper bound for the rectangle.** The rectangle's modulus is at most
`ENNReal.ofReal ((t − s)/(b − a))`. The constant density `(1/(b−a))·𝟙_R` on the
rectangle is admissible for the connecting curve family (the projection inequality:
every absolutely continuous curve from the left to the right side has real-part
increment `b − a ≤` its arc length), and its energy is exactly `(t−s)/(b−a)`. -/
theorem axisRect_modulus_upper_bound {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateral a b s t hab hst).modulus
      ≤ ENNReal.ofReal ((t - s) / (b - a)) := by
  unfold Quadrilateral.modulus curveModulus
  calc ⨅ ρ ∈ {ρ : ℂ → ℝ≥0∞ | IsAdmissibleDensity ρ
          (axisRectQuadrilateral a b s t hab hst).curveFamily}, ∫⁻ z, (ρ z) ^ 2
      ≤ ∫⁻ z, (axisRectDensity a b s t z) ^ 2 :=
        iInf₂_le (axisRectDensity a b s t) (axisRectDensity_admissible hab hst)
    _ = ENNReal.ofReal ((t - s) / (b - a)) := lintegralSq_axisRectDensity hab hst

/-- **The modulus of the axis-aligned rectangle** `[a, b] × [s, t]` is exactly
`(t − s)/(b − a)`. This is the foundational input to the reverse length–area
inequality `∫ ℓ_f(y)² dy ≤ K · area(f(R))`. -/
theorem axisRect_modulus {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateral a b s t hab hst).modulus
      = ENNReal.ofReal ((t - s) / (b - a)) :=
  le_antisymm (axisRect_modulus_upper_bound hab hst) (axisRect_modulus_lower_bound hab hst)

/-! ## The image-family modulus bound for axis rectangles

The geometric quasiconformality hypothesis `hf.2.2`, specialised to the axis rectangle
`R = (a, b) × (s, t)` and combined with the exact rectangle modulus `axisRect_modulus`,
gives the concrete distortion bound `M(f(R)) ≤ K · (t − s)/(b − a)`. This is the entry
point of the reverse length–area extraction: the left-hand side is an explicit modulus of
an image curve family, and every density admissible for that family feeds the energy
estimate. -/

/-- **Image-modulus bound for an axis rectangle (raw `ENNReal` product form).** For a
geometric `K`-quasiconformal map `f`, the modulus of the image connecting family of the
axis rectangle `R = (a, b) × (s, t)` is at most `K · (t − s)/(b − a)`, written as the
product `ENNReal.ofReal K * ENNReal.ofReal ((t − s)/(b − a))`. This is the geometric
hypothesis `hf.2.2` specialised to `axisRectQuadrilateral`, with the source modulus
rewritten by `axisRect_modulus`. -/
theorem axisRect_imageModulus_le {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f)
      ≤ ENNReal.ofReal K * ENNReal.ofReal ((t - s) / (b - a)) := by
  have hmod := hf.2.2 (axisRectQuadrilateral a b s t hab hst)
  rwa [axisRect_modulus hab hst] at hmod

/-- **Image-modulus bound for an axis rectangle (collapsed `ofReal` form).** The product
of nonnegative reals collapses: for a geometric `K`-quasiconformal map `f` (so `0 ≤ K`),
the image-family modulus of the rectangle `R = (a, b) × (s, t)` is at most
`ENNReal.ofReal (K · (t − s)/(b − a))`. This is the single real number bounding the energy
of any admissible density for the image family — the quantity the reverse length–area
energy estimate is compared against. -/
theorem axisRect_imageModulus_le_ofReal {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f)
      ≤ ENNReal.ofReal (K * ((t - s) / (b - a))) := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hf.1
  rw [ENNReal.ofReal_mul hK0]
  exact axisRect_imageModulus_le hf hab hst

/-! ### The swapped axis-rectangle quadrilateral (structural bricks)

The **swapped** axis-rectangle parametrises the rectangle so its left/right sides are the
bottom/top edges. Its connecting family is therefore the *separating* (bottom ↔ top) family
of the rectangle — the conjugate of the standard crossing family. The structural lemmas
(`*_image`, `*_leftSide`, `*_rightSide`, `*_toFun`) are placed here so downstream files —
including `QC/GeometricToAnalytic/LoewnerReciprocity.lean` (the planar reciprocity workstream) — can
reference
the swapped quadrilateral without depending on the heavy
`QC/GeometricToAnalytic/GeometricDifferentiable/`.
The admissibility / modulus upper bound for the swapped variant
(`axisRectDensitySwap_admissible`, `axisRectSwap_modulus_upper_bound`) live in
`QC/GeometricToAnalytic/GeometricDifferentiable/` (they consume `funcIncrement_le_arcLength`, which
is
also there). -/

/-- The **swapped** axis-rectangle quadrilateral: the parametrization
`⟨x, y⟩ ↦ ⟨a + (b−a)·y, s + (t−s)·x⟩` of the unit square onto `[a, b] × [s, t]`, i.e. the standard
`axisRectMap` precomposed with the coordinate swap `Prod.swap`. Its **left** side is the *bottom*
edge `[a, b] × {s}`, its **right** side is the *top* edge `[a, b] × {t}`, and its image region is
the same rectangle `[a, b] × [s, t]`. Its connecting (crossing) family is therefore the *separating*
(bottom ↔ top) family of the rectangle — the conjugate of the standard crossing family. -/
noncomputable def axisRectQuadrilateralSwap (a b s t : ℝ) (hab : a < b) (hst : s < t) :
    Quadrilateral where
  toFun := axisRectMap a b s t ∘ Prod.swap
  continuous_toFun := (axisRectMap_continuous a b s t).comp continuous_swap
  injOn_unitSquare := by
    intro p hp q hq h
    have hswap : unitSquare = Prod.swap ⁻¹' unitSquare := by
      ext w; simp only [unitSquare, Set.mem_preimage, Set.mem_prod, Prod.fst_swap, Prod.snd_swap]
      exact and_comm
    have hps : Prod.swap p ∈ unitSquare := by rw [hswap] at hp; exact hp
    have hqs : Prod.swap q ∈ unitSquare := by rw [hswap] at hq; exact hq
    have := axisRectMap_injOn hab hst hps hqs h
    exact Prod.swap_injective this

@[simp] theorem axisRectQuadrilateralSwap_toFun (a b s t : ℝ) (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateralSwap a b s t hab hst).toFun = axisRectMap a b s t ∘ Prod.swap := rfl

/-- The image region of the swapped rectangle quadrilateral is the same rectangle `[a, b] × [s, t]`
as the unswapped one: the coordinate swap is a bijection of the unit square. -/
theorem axisRectQuadrilateralSwap_image {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateralSwap a b s t hab hst).image
      = (axisRectQuadrilateral a b s t hab hst).image := by
  rw [Quadrilateral.image, Quadrilateral.image, axisRectQuadrilateralSwap_toFun,
    axisRectQuadrilateral_toFun, Set.image_comp]
  congr 1
  -- `swap '' unitSquare = unitSquare`, since `swap` is a self-bijection of the (symmetric) square.
  rw [unitSquare, Set.image_swap_prod]

/-- The left side of the swapped rectangle is its *bottom* edge `{z | s ≤ z.im, z.re ∈ [a, b],
z.im = s}`. -/
theorem axisRectQuadrilateralSwap_leftSide {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateralSwap a b s t hab hst).leftSide
      = {z : ℂ | z.im = s ∧ (a ≤ z.re ∧ z.re ≤ b)} := by
  have hbma : (0:ℝ) < b - a := by linarith
  ext z
  simp only [Quadrilateral.leftSide, axisRectQuadrilateralSwap_toFun, Function.comp_apply,
    axisRectMap, Set.mem_image, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc, Set.mem_ofPred_eq,
    Prod.fst_swap, Prod.snd_swap, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨rfl, hx0, hx1⟩, rfl⟩
    refine ⟨by dsimp only [Complex.im]; ring, ?_, ?_⟩ <;>
      dsimp only [Complex.re] <;> nlinarith
  · rintro ⟨him, hre0, hre1⟩
    refine ⟨0, (z.re - a)/(b - a), ⟨rfl, ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) hbma.le
    · rw [div_le_one hbma]; linarith
    · apply Complex.ext <;> dsimp only [Complex.re, Complex.im]
      · field_simp; ring
      · rw [mul_zero, add_zero]; exact him.symm

/-- The right side of the swapped rectangle is its *top* edge `{z | z.im = t, z.re ∈ [a, b]}`. -/
theorem axisRectQuadrilateralSwap_rightSide {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateralSwap a b s t hab hst).rightSide
      = {z : ℂ | z.im = t ∧ (a ≤ z.re ∧ z.re ≤ b)} := by
  have hbma : (0:ℝ) < b - a := by linarith
  ext z
  simp only [Quadrilateral.rightSide, axisRectQuadrilateralSwap_toFun, Function.comp_apply,
    axisRectMap, Set.mem_image, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc, Set.mem_ofPred_eq,
    Prod.fst_swap, Prod.snd_swap, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨rfl, hx0, hx1⟩, rfl⟩
    refine ⟨by dsimp only [Complex.im]; ring, ?_, ?_⟩ <;>
      dsimp only [Complex.re] <;> nlinarith
  · rintro ⟨him, hre0, hre1⟩
    refine ⟨1, (z.re - a)/(b - a), ⟨rfl, ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) hbma.le
    · rw [div_le_one hbma]; linarith
    · apply Complex.ext <;> dsimp only [Complex.re, Complex.im]
      · field_simp; ring
      · rw [mul_one]; linarith [him]

/-! ### The axis-rectangle modulus-bound hypothesis (the parametrized QC input)

The entire forward length–area chain (the Bishop bricks in `QC/LengthArea/Bishop*.lean` and the
residual chain in `QC/LengthArea/ReverseLengthAreaEnergy.lean`) consumes the geometric
quasiconformality hypothesis `IsQCGeometric f K` **only** through three facts: `1 ≤ K`, `f` is a
homeomorphism, and the image-family modulus bounds on the (crossing and separating families of)
axis rectangles. `AxisRectModulusBound` packages exactly these facts, so the chain can be
instantiated at maps that are not known to be quasiconformal on *all* quadrilaterals — in
particular at the **inverse** `g = f⁻¹` of a geometric quasiconformal map, whose axis-rectangle
bounds are produced by the explicit-density length–area argument
(`IsQCGeometric.inverse_axisRectModulusBound` in
`QC/GeometricToAnalytic/NondegeneracyAssembly.lean`) without any two-sided modulus reciprocity.
-/

/-- **The axis-rectangle modulus-bound hypothesis.** `AxisRectModulusBound f K` holds when
`1 ≤ K`, `f` is a homeomorphism of `ℂ`, and for every axis rectangle `R = (a, b) × (s, t)` the
image connecting family of the standard (crossing) parametrization has modulus at most
`K·(t − s)/(b − a)` and the image connecting family of the swapped (separating) parametrization
has modulus at most `K·(b − a)/(t − s)`.

This is precisely the sub-hypothesis of `IsQCGeometric f K` that the forward length–area /
ACL chain consumes (see `IsQCGeometric.toAxisRectModulusBound`); it is strictly weaker — it
mentions only axis rectangles, never general quadrilaterals — which is what makes it provable
for the inverse map by the length–area transfer with the explicit admissible density
`ρ = 𝟙_{g(R̄)}·‖Df‖/(b−a)` (Lehto–Virtanen's rectangle estimate, no reciprocity). -/
def AxisRectModulusBound (f : ℂ → ℂ) (K : ℝ) : Prop :=
  1 ≤ K ∧ IsHomeomorph f ∧
    (∀ (a b s t : ℝ) (hab : a < b) (hst : s < t),
        curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f)
          ≤ ENNReal.ofReal (K * ((t - s) / (b - a)))) ∧
    (∀ (a b s t : ℝ) (hab : a < b) (hst : s < t),
        curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)
          ≤ ENNReal.ofReal (K * ((b - a) / (t - s))))

namespace AxisRectModulusBound

variable {f : ℂ → ℂ} {K : ℝ}

/-- The constant of an axis-rectangle modulus bound is at least one. -/
theorem one_le (hf : AxisRectModulusBound f K) : 1 ≤ K := hf.1

/-- A map with an axis-rectangle modulus bound is a homeomorphism. -/
theorem isHomeomorph (hf : AxisRectModulusBound f K) : IsHomeomorph f := hf.2.1

/-- **Crossing bound, product form.** The image-family modulus of the standard axis-rectangle
parametrization is at most `ENNReal.ofReal K * ENNReal.ofReal ((t − s)/(b − a))` — the split
`ℝ≥0∞`-product form the Rengel bricks consume. -/
theorem axisRect_le (hf : AxisRectModulusBound f K) {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f)
      ≤ ENNReal.ofReal K * ENNReal.ofReal ((t - s) / (b - a)) := by
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one hf.1)]
  exact hf.2.2.1 a b s t hab hst

/-- **Separating bound, product form.** The image-family modulus of the swapped axis-rectangle
parametrization is at most `ENNReal.ofReal K * ENNReal.ofReal ((b − a)/(t − s))`. -/
theorem axisRectSwap_le (hf : AxisRectModulusBound f K) {a b s t : ℝ} (hab : a < b)
    (hst : s < t) :
    curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)
      ≤ ENNReal.ofReal K * ENNReal.ofReal ((b - a) / (t - s)) := by
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one hf.1)]
  exact hf.2.2.2 a b s t hab hst

end AxisRectModulusBound

end NoWanderingDomains
