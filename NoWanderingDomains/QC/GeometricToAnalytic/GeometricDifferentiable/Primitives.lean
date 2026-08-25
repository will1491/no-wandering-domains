/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Geometric
import NoWanderingDomains.QC.Defs.SensePreserving
import NoWanderingDomains.QC.LengthArea.ReverseLengthAreaForward
import NoWanderingDomains.QC.GeometricToAnalytic.ModulusSymmetrization
import NoWanderingDomains.Analysis.Sobolev.Stepanov
import NoWanderingDomains.Analysis.Sobolev.Coarea.Assembly
import NoWanderingDomains.Hyperbolic.WindingNumber.CircleRectangleWinding
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Analysis.ConstantSpeed
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Foundational primitives for the geometric reverse-length–area / reciprocity development

This file collects the elementary, reusable primitives on which the geometric ⇒ analytic
reverse-length–area machinery is built; the higher-level development lives in the sibling files
`PlaneSeparation`, `RectifiablePathHelpers`, and `Reciprocity`.

## Contents

* **STEP 1 — ball ↔ axis squares.** The closed ball `closedBall x r` is sandwiched between its
  inscribed axis square `qcInnerSquare x r` (half-side `r/√2`, corners on the circle) and
  circumscribed axis square `qcOuterSquare x r` (half-side `r`); these inclusions and their images
  are elementary plane geometry, with no quasiconformal content.

* **STEP 2 — Rengel's inequality.** The length–area area lower bound `rengel_area_lower_bound`:
  for a curve family `Γ` whose curves connect two sets at distance `≥ d` while staying inside a
  measurable region `R`, `d² · M(Γ) ≤ area(R)`, via the admissible density `(1/d)·𝟙_R` (each
  connecting curve has arc length `≥` chord `≥ d`). This turns a modulus *lower* bound into an
  area *lower* bound.

* **STEP 3 — conjugate-square modulus reciprocity reduction.** The swapped square
  `axisRectQuadrilateralSwap` and its structural lemmas, the Rengel finiteness witnesses
  `imageCurveFamily_finiteWitness`, and the `ℝ≥0∞` lemma `one_le_biInf_mul_biInf'` that turns the
  per-density length–area inequality into modulus reciprocity. The reciprocity itself is assembled
  in `Reciprocity` and bottoms out at the planar Loewner residual
  `loewner_image_cross_bound_axisRect`.

* **Reusable primitives** — Hausdorff / co-area, measure-theory / path-algebra, and
  path-concatenation / affine-reparametrization machinery used across the development.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal Real

namespace NoWanderingDomains

/-! ## STEP 1 — the ball and its two concentric axis squares

The Euclidean closed ball `closedBall x r` sits between two concentric axis-aligned squares:
the inscribed square `qcInnerSquare x r` of half-side `r/√2` (its far corner lies exactly on the
circle of radius `r`) and the circumscribed square `qcOuterSquare x r` of half-side `r`. For a
homeomorphism — in particular injective with continuous, hence compact, images — these set
inclusions transport to the images, and `Metric.diam`/`volume` are monotone under inclusion. All
lemmas of this section are elementary plane geometry; they carry no quasiconformal content. -/

/-- The inscribed axis-aligned square of the ball `closedBall x r`: the closed axis square centred
at `x` with half-side `r/√2`. Its four corners lie on the circle of radius `r`, so it is contained
in the ball. -/
noncomputable def qcInnerSquare (x : ℂ) (r : ℝ) : Set ℂ :=
  axisRect (x.re - r / Real.sqrt 2) (x.re + r / Real.sqrt 2)
    (x.im - r / Real.sqrt 2) (x.im + r / Real.sqrt 2)

/-- The circumscribed axis-aligned square of the ball `closedBall x r`: the closed axis square
centred at `x` with half-side `r`. It contains the ball, since `|z.re − x.re| ≤ ‖z − x‖` and
`|z.im − x.im| ≤ ‖z − x‖`. -/
noncomputable def qcOuterSquare (x : ℂ) (r : ℝ) : Set ℂ :=
  axisRect (x.re - r) (x.re + r) (x.im - r) (x.im + r)

/-- **Inscribed square ⊆ ball.** Every point of the inner axis square (half-side `r/√2`) is within
distance `r` of the centre: `(z.re−x.re)² + (z.im−x.im)² ≤ (r/√2)² + (r/√2)² = r²`. -/
theorem qcInnerSquare_subset_closedBall (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    qcInnerSquare x r ⊆ Metric.closedBall x r := by
  intro z hz
  simp only [qcInnerSquare, axisRect, Set.mem_ofPred_eq] at hz
  obtain ⟨⟨hre0, hre1⟩, him0, him1⟩ := hz
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  -- Coordinate bounds: `|z.re − x.re| ≤ r/√2` and `|z.im − x.im| ≤ r/√2`.
  have hreabs : |z.re - x.re| ≤ r / Real.sqrt 2 := by
    rw [abs_le]; constructor <;> linarith
  have himabs : |z.im - x.im| ≤ r / Real.sqrt 2 := by
    rw [abs_le]; constructor <;> linarith
  -- `(r/√2)² = r²/2`.
  have hhalf : (r / Real.sqrt 2) ^ 2 = r ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [Metric.mem_closedBall, Complex.dist_eq_re_im]
  rw [show √((z.re - x.re) ^ 2 + (z.im - x.im) ^ 2) ≤ r
      ↔ (z.re - x.re) ^ 2 + (z.im - x.im) ^ 2 ≤ r ^ 2 from Real.sqrt_le_left hr]
  have h1 : (z.re - x.re) ^ 2 ≤ r ^ 2 / 2 := by
    rw [← hhalf]; exact sq_le_sq' (by linarith [abs_le.1 hreabs]) (abs_le.1 hreabs).2
  have h2 : (z.im - x.im) ^ 2 ≤ r ^ 2 / 2 := by
    rw [← hhalf]; exact sq_le_sq' (by linarith [abs_le.1 himabs]) (abs_le.1 himabs).2
  linarith

/-- **Ball ⊆ circumscribed square.** For `z` in `closedBall x r`, both coordinate deviations are
bounded by `‖z − x‖ ≤ r`: `|z.re − x.re| ≤ ‖z − x‖` and `|z.im − x.im| ≤ ‖z − x‖`. -/
theorem closedBall_subset_qcOuterSquare (x : ℂ) (r : ℝ) :
    Metric.closedBall x r ⊆ qcOuterSquare x r := by
  intro z hz
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  simp only [qcOuterSquare, axisRect, Set.mem_ofPred_eq]
  have hre : |(z - x).re| ≤ ‖z - x‖ := Complex.abs_re_le_norm _
  have him : |(z - x).im| ≤ ‖z - x‖ := Complex.abs_im_le_norm _
  simp only [Complex.sub_re, Complex.sub_im] at hre him
  rw [abs_le] at hre him
  refine ⟨⟨by linarith [hre.1, hz], by linarith [hre.2, hz]⟩,
    by linarith [him.1, hz], by linarith [him.2, hz]⟩

/-- The inner square's image is contained in the ball's image (`f` need only be a map). -/
theorem image_qcInnerSquare_subset (f : ℂ → ℂ) (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    f '' qcInnerSquare x r ⊆ f '' Metric.closedBall x r :=
  Set.image_mono (qcInnerSquare_subset_closedBall x hr)

/-- The ball's image is contained in the outer square's image. -/
theorem image_closedBall_subset_qcOuterSquare (f : ℂ → ℂ) (x : ℂ) (r : ℝ) :
    f '' Metric.closedBall x r ⊆ f '' qcOuterSquare x r :=
  Set.image_mono (closedBall_subset_qcOuterSquare x r)

/-- The circumscribed square is contained in `closedBall x (2r)` (since `‖z − x‖ ≤ |z.re − x.re| +
|z.im − x.im| ≤ 2r`), hence is bounded; combined with closedness it is compact. -/
theorem isCompact_qcOuterSquare (x : ℂ) (r : ℝ) : IsCompact (qcOuterSquare x r) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · -- closed: an intersection of four closed coordinate half-planes.
    simp only [qcOuterSquare, axisRect, Set.ofPred_and]
    exact ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))
  · -- bounded: contained in `closedBall x (2r)`.
    refine (Metric.isBounded_closedBall (x := x) (r := 2 * r)).subset (fun z hz => ?_)
    simp only [qcOuterSquare, axisRect, Set.mem_ofPred_eq] at hz
    obtain ⟨⟨hre0, hre1⟩, him0, him1⟩ := hz
    rw [Metric.mem_closedBall, Complex.dist_eq]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have hre : |z.re - x.re| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
    have him : |z.im - x.im| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
    linarith

/-! ## STEP 2 — Rengel's inequality (the elementary length–area area lower bound)

**Rengel's inequality** `rengel_area_lower_bound`: for a curve family `Γ` whose curves connect two
sets `A₁, A₂` at distance `≥ d` while staying inside a measurable region `R`, `d² · M(Γ) ≤ area(R)`.
The proof is the admissible-density argument (template: `axisRect_modulus_upper_bound`): the density
`(1/d)·𝟙_R` is admissible (each connecting curve has arc length `≥` chord `≥ d`), so
`M(Γ) ≤ ∫ ρ² = area(R)/d²`. This turns a modulus *lower* bound into an area *lower* bound, and is
the elementary length–area input to the reciprocity reduction (STEP 3). -/

/-- **Functional-increment ≤ arc length.** For an absolutely continuous curve `δ : ℝ → ℂ` on
`[0, 1]` and a real-linear continuous functional `L : ℂ →L[ℝ] ℝ` of operator norm `≤ 1`, the
increment `L(δ 1) − L(δ 0)` is at most the total arc length `∫₀¹ ‖δ'‖`. The projection inequality
`|L(δ')| ≤ ‖L‖ · ‖δ'‖ ≤ ‖δ'‖` integrated through the fundamental theorem of calculus for the
absolutely continuous real function `L ∘ δ`. (Generalizes `reIncrement_le_arcLength`, which is the
case `L = Complex.reCLM`.) -/
theorem funcIncrement_le_arcLength {δ : ℝ → ℂ}
    (hδac : AbsolutelyContinuousOnInterval δ 0 1) (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    ENNReal.ofReal (L (δ 1) - L (δ 0))
      ≤ ∫⁻ t in Set.Icc (0:ℝ) 1, (‖deriv δ t‖₊ : ℝ≥0∞) := by
  set g : ℝ → ℝ := fun t => L (δ t) with hg_def
  have hg_ac : AbsolutelyContinuousOnInterval g 0 1 := by
    have hl : ∀ {F : ℝ → ℂ} {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (k : NNReal),
        LipschitzWith k l → ∀ {a c : ℝ}, AbsolutelyContinuousOnInterval F a c →
        AbsolutelyContinuousOnInterval (fun t => l (F t)) a c := by
      intro F Y _ l k hl a c hF
      rw [absolutelyContinuousOnInterval_iff] at hF ⊢
      intro ε hε
      obtain ⟨δ', hδ', hδ''⟩ := hF (ε / (k + 1)) (by positivity)
      refine ⟨δ', hδ', fun E hE hlen => ?_⟩
      have key := hδ'' E hE hlen
      have hknn : (0 : ℝ) ≤ (k : ℝ) := k.coe_nonneg
      calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
          ≤ ∑ i ∈ Finset.range E.1, (k : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
            Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
        _ = (k : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
            rw [Finset.mul_sum]
        _ ≤ (k : ℝ) * (ε / (k + 1)) := mul_le_mul_of_nonneg_left key.le hknn
        _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hknn]
    exact hl L ‖L‖₊ L.lipschitz hδac
  have hg_int : IntervalIntegrable (deriv g) volume 0 1 := hg_ac.intervalIntegrable_deriv
  have hftc : ∫ t in (0:ℝ)..1, deriv g t = L (δ 1) - L (δ 0) := hg_ac.integral_deriv_eq_sub
  have hioc : ∫ t in (0:ℝ)..1, deriv g t = ∫ t in Set.Ioc (0:ℝ) 1, deriv g t :=
    intervalIntegral.integral_of_le (by norm_num)
  have hg_int' : IntegrableOn (deriv g) (Set.Ioc (0:ℝ) 1) volume := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hg_int
    exact hg_int
  have hbound1 : ENNReal.ofReal (L (δ 1) - L (δ 0))
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
  have hδ_diff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ δ t :=
    hδac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  have hbound2 : ∫⁻ t in Set.Ioc (0:ℝ) 1, (‖deriv g t‖₊ : ℝ≥0∞)
      ≤ ∫⁻ t in Set.Ioc (0:ℝ) 1, (‖deriv δ t‖₊ : ℝ≥0∞) := by
    apply lintegral_mono_ae
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hδ_diff] with t htdiff htmem
    have hd : DifferentiableAt ℝ δ t :=
      htdiff (Set.mem_uIcc.mpr (Or.inl (Set.Ioc_subset_Icc_self htmem)))
    have hderiv_g : deriv g t = L (deriv δ t) := by
      have hh : HasDerivAt g (L (deriv δ t)) t := by
        have := L.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt
        simpa [hg_def] using! this
      exact hh.deriv
    rw [hderiv_g, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    calc ‖L (deriv δ t)‖ ≤ ‖L‖ * ‖deriv δ t‖ := L.le_opNorm _
      _ ≤ 1 * ‖deriv δ t‖ := by gcongr
      _ = ‖deriv δ t‖ := one_mul _
  refine hbound1.trans (hbound2.trans ?_)
  exact lintegral_mono_set Set.Ioc_subset_Icc_self

/-- The norm-`≤ 1` functional realizing the norm of a complex number `w`: as a real-linear
continuous map `ℂ →L[ℝ] ℝ`, `v ↦ ‖w‖⁻¹ · Re(conj w · v)`. It sends `w` to `‖w‖` (so it witnesses
`‖w‖` as a `1`-Lipschitz projection), used to derive `chord_le_arcLength`. -/
noncomputable def normFunctional (w : ℂ) : ℂ →L[ℝ] ℝ :=
  (‖w‖⁻¹ : ℝ) • (Complex.reCLM.comp
    ((ContinuousLinearMap.mul ℝ ℂ (starRingEnd ℂ w)).restrictScalars ℝ))

/-- The defining formula: `normFunctional w v = ‖w‖⁻¹ · Re(conj w · v)`. -/
theorem normFunctional_apply (w v : ℂ) :
    normFunctional w v = ‖w‖⁻¹ * ((starRingEnd ℂ w) * v).re := by
  simp [normFunctional]

/-- `normFunctional w` sends `w` to its norm: `normFunctional w w = ‖w‖` (for `w ≠ 0`). -/
theorem normFunctional_self {w : ℂ} (hw : w ≠ 0) : normFunctional w w = ‖w‖ := by
  rw [normFunctional_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    show w.re * w.re - -w.im * w.im = Complex.normSq w by rw [Complex.normSq_apply]; ring,
    Complex.normSq_eq_norm_sq]
  field_simp

/-- `normFunctional w` is `1`-Lipschitz: its operator norm is at most `1`. -/
theorem norm_normFunctional_le (w : ℂ) : ‖normFunctional w‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [normFunctional_apply, one_mul]
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_norm, inv_mul_le_iff₀ (by positivity)]
    calc |((starRingEnd ℂ w) * v).re| ≤ ‖(starRingEnd ℂ w) * v‖ := Complex.abs_re_le_norm _
      _ = ‖w‖ * ‖v‖ := by rw [norm_mul, RCLike.norm_conj]

/-- **Chord ≤ arc length.** For an absolutely continuous curve `δ : ℝ → ℂ` on `[0, 1]`, the
straight-line chord distance `‖δ 1 − δ 0‖` is at most the total arc length `∫₀¹ ‖δ'‖`. Obtained from
`funcIncrement_le_arcLength` with the `1`-Lipschitz functional `normFunctional (δ 1 − δ 0)`, which
sends the chord vector to its own norm. -/
theorem chord_le_arcLength {δ : ℝ → ℂ} (hδac : AbsolutelyContinuousOnInterval δ 0 1) :
    ENNReal.ofReal ‖δ 1 - δ 0‖
      ≤ ∫⁻ t in Set.Icc (0:ℝ) 1, (‖deriv δ t‖₊ : ℝ≥0∞) := by
  rcases eq_or_ne (δ 1 - δ 0) 0 with hz | hz
  · rw [hz, norm_zero, ENNReal.ofReal_zero]; exact zero_le
  · set w : ℂ := δ 1 - δ 0 with hw
    have hkey := funcIncrement_le_arcLength hδac (normFunctional w) (norm_normFunctional_le w)
    have hval : normFunctional w (δ 1) - normFunctional w (δ 0) = ‖w‖ := by
      rw [← map_sub, ← hw, normFunctional_self hz]
    rwa [hval] at hkey

/-- The **Rengel density** `(1/d)·𝟙_R` is admissible for any curve family `Γ` whose curves connect
two sets `A₁, A₂` at distance `≥ d` while staying inside the measurable region `R`. The
admissibility computation: along each curve the indicator is `1`, so its arc-length line integral is
`(1/d) · ∫ ‖δ'‖ ≥ (1/d) · ‖δ 1 − δ 0‖ ≥ (1/d) · d = 1`, using `chord_le_arcLength` and that
endpoints lie at distance `≥ d`. The template is `axisRectDensity_admissible`. -/
theorem rengelDensity_admissible {R : Set ℂ} (hRmeas : MeasurableSet R)
    {A₁ A₂ : Set ℂ} {d : ℝ} (hd : 0 < d)
    (hdist : ∀ p ∈ A₁, ∀ q ∈ A₂, d ≤ dist p q)
    {Γ : Set (ℝ → ℂ)}
    (hΓ : ∀ δ ∈ Γ, Continuous δ ∧ AbsolutelyContinuousOnInterval δ 0 1 ∧
      δ 0 ∈ A₁ ∧ δ 1 ∈ A₂ ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ R) :
    IsAdmissibleDensity (R.indicator (fun _ => ENNReal.ofReal (1 / d))) Γ := by
  refine ⟨Measurable.indicator measurable_const hRmeas, ?_⟩
  intro δ hδ
  obtain ⟨hδcont, hδac, hδ0, hδ1, hδimg⟩ := hΓ δ hδ
  have harc : arcLengthLineIntegral (R.indicator (fun _ => ENNReal.ofReal (1 / d))) δ
      = ENNReal.ofReal (1 / d) * ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv δ u‖₊ : ℝ≥0∞) := by
    unfold arcLengthLineIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    simp only
    rw [Set.indicator_of_mem (hδimg u hu)]
  rw [harc]
  have hchord : ENNReal.ofReal d ≤ ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv δ u‖₊ : ℝ≥0∞) := by
    have hdle : d ≤ ‖δ 1 - δ 0‖ := by
      rw [← dist_eq_norm, dist_comm]; exact hdist (δ 0) hδ0 (δ 1) hδ1
    exact le_trans (ENNReal.ofReal_le_ofReal hdle) (chord_le_arcLength hδac)
  calc (1 : ℝ≥0∞)
      = ENNReal.ofReal (1 / d) * ENNReal.ofReal d := by
        rw [← ENNReal.ofReal_mul (by positivity), one_div,
          inv_mul_cancel₀ (ne_of_gt hd), ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (1 / d) * ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv δ u‖₊ : ℝ≥0∞) := by gcongr

/-- **Rengel's inequality (area lower bound).** For a curve family `Γ` whose curves connect two sets
`A₁, A₂` at distance `≥ d` while staying inside the measurable region `R`,
`d² · M(Γ) ≤ area(R)`. The admissible Rengel density `(1/d)·𝟙_R` bounds `M(Γ) ≤ area(R)/d²`;
clearing denominators gives the area lower bound. This is the length–area / extremal-length module
estimate, in the form that converts a modulus *lower* bound into an area *lower* bound. -/
theorem rengel_area_lower_bound {R : Set ℂ} (hRmeas : MeasurableSet R)
    {A₁ A₂ : Set ℂ} {d : ℝ} (hd : 0 < d)
    (hdist : ∀ p ∈ A₁, ∀ q ∈ A₂, d ≤ dist p q)
    {Γ : Set (ℝ → ℂ)}
    (hΓ : ∀ δ ∈ Γ, Continuous δ ∧ AbsolutelyContinuousOnInterval δ 0 1 ∧
      δ 0 ∈ A₁ ∧ δ 1 ∈ A₂ ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ R) :
    ENNReal.ofReal (d ^ 2) * curveModulus Γ ≤ volume R := by
  set ρ₀ : ℂ → ℝ≥0∞ := R.indicator (fun _ => ENNReal.ofReal (1 / d)) with hρ₀
  have hadm := rengelDensity_admissible hRmeas hd hdist hΓ
  have hmod_le : curveModulus Γ ≤ ∫⁻ z, (ρ₀ z) ^ 2 := iInf₂_le ρ₀ hadm
  have henergy : ∫⁻ z, (ρ₀ z) ^ 2 = ENNReal.ofReal (1 / d ^ 2) * volume R := by
    have hsq : (fun z => (ρ₀ z) ^ 2)
        = R.indicator (fun _ => ENNReal.ofReal (1 / d) ^ 2) := by
      funext z; rw [hρ₀]; by_cases hz : z ∈ R <;> simp [hz]
    have hscalar : ENNReal.ofReal (1 / d) ^ 2 = ENNReal.ofReal (1 / d ^ 2) := by
      rw [← ENNReal.ofReal_pow (by positivity), div_pow, one_pow]
    rw [hsq, lintegral_indicator hRmeas, setLIntegral_const, hscalar, mul_comm]
  rw [henergy] at hmod_le
  calc ENNReal.ofReal (d ^ 2) * curveModulus Γ
      ≤ ENNReal.ofReal (d ^ 2) * (ENNReal.ofReal (1 / d ^ 2) * volume R) := by gcongr
    _ = volume R := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          mul_one_div, div_self (by positivity), ENNReal.ofReal_one, one_mul]

/-! ## STEP 3 — the genuinely two-dimensional quasiconformal estimates

After Rengel, the remaining estimates are genuinely two-dimensional and classically absent from
Mathlib (the conjugate square and modulus reciprocity); they are developed below. -/

/-! ### The conjugate (swapped) square and modulus reciprocity

The modulus *lower* bound `M(Γ) ≥ 1/K` for the image crossing family `Γ` of a square is obtained
from **modulus reciprocity**: a square has two *conjugate* families — the crossing family `Γ`
(left ↔ right) and the separating family `Γ*` (bottom ↔ top). For their `f`-images one has the
reciprocity `M(Γ) · M(Γ*) ≥ 1`, and the geometric upper bound applied to the *swapped* square gives
`M(Γ*) ≤ K · 1 = K`; combining, `M(Γ) ≥ 1/M(Γ*) ≥ 1/K`.

The conjugate family `Γ*` is realized as the image crossing family of the **swapped** square
`axisRectQuadrilateralSwap`, whose left/right sides are the bottom/top of the rectangle. Its modulus
*upper* bound — all we need to instantiate `M(Γ*) ≤ K` — is the swapped analogue of
`axisRect_modulus_upper_bound` and is carried out in full below (the admissible density
`(1/(t−s))·𝟙_R`, with the imaginary-part projection inequality
`funcIncrement_le_arcLength … Complex.imCLM`). The one genuinely two-dimensional input is the
reciprocity inequality itself, `conjugateImageModulus_reciprocity` (assembled in `Reciprocity`,
bottoming out at the planar Loewner residual `loewner_image_cross_bound_axisRect`).

The swapped axis-rectangle quadrilateral itself and its structural lemmas
(`axisRectQuadrilateralSwap`, `*_{image,leftSide,rightSide,toFun}`) live in
`QC/LengthArea/ReverseLengthAreaForward.lean` so the planar Loewner-reciprocity workstream
(`QC/GeometricToAnalytic/LoewnerReciprocity.lean`) can reference the swap without depending on this
heavy
file. The admissibility / modulus upper-bound bricks
(`axisRectDensitySwap_admissible`, `axisRectSwap_modulus_upper_bound`) are kept here
because they consume `funcIncrement_le_arcLength` (above), which lives in this file. -/

/-- The constant density `(1/(t−s))·𝟙_R` on the rectangle is **admissible** for the swapped
(bottom ↔ top) connecting family: every absolutely continuous curve from the bottom side to the top
side staying in the rectangle has imaginary-part increment `t − s ≤` its arc length (the projection
inequality `funcIncrement_le_arcLength` with the norm-`1` functional `Complex.imCLM`), so its
arc-length line integral is `≥ (1/(t−s))·(t−s) = 1`. This is the swapped analogue of
`axisRectDensity_admissible`. -/
theorem axisRectDensitySwap_admissible {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    IsAdmissibleDensity
      ((axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (t - s))))
      (axisRectQuadrilateralSwap a b s t hab hst).curveFamily := by
  have htms : (0:ℝ) < t - s := by linarith
  refine ⟨Measurable.indicator measurable_const (measurableSet_axisRect a b s t), ?_⟩
  rintro γ ⟨hγcont, hγac, hγ0, hγ1, hγimg⟩
  -- The endpoints lie on the bottom/top sides: `Im(γ 0) = s`, `Im(γ 1) = t`.
  rw [axisRectQuadrilateralSwap_leftSide] at hγ0
  rw [axisRectQuadrilateralSwap_rightSide] at hγ1
  obtain ⟨hγ0im, _⟩ := hγ0
  obtain ⟨hγ1im, _⟩ := hγ1
  -- On `[0, 1]`, `γ t` is in the rectangle, so the density there is `ofReal (1/(t−s))`.
  have hγimg' : ∀ u ∈ Set.Icc (0:ℝ) 1, γ u ∈ axisRect a b s t := by
    intro u hu
    have hmem := hγimg u hu
    rw [axisRectQuadrilateralSwap_image, axisRectQuadrilateral_image] at hmem
    exact hmem
  have hργ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      (axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (t - s))) (γ u)
        = ENNReal.ofReal (1 / (t - s)) := by
    intro u hu
    rw [Set.indicator_of_mem (hγimg' u hu)]
  have harc : arcLengthLineIntegral
      ((axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (t - s)))) γ
      = ENNReal.ofReal (1 / (t - s)) * ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv γ u‖₊ : ℝ≥0∞) := by
    unfold arcLengthLineIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    simp only
    rw [hργ u hu]
  rw [harc]
  -- Imaginary-part increment `t − s ≤ ∫⁻ ‖γ'‖`, so the product is `≥ 1`.
  have hincr : ENNReal.ofReal (t - s)
      ≤ ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv γ u‖₊ : ℝ≥0∞) := by
    have hnorm : ‖Complex.imCLM‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
        simpa only [Complex.imCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_im_le_norm v
    have := funcIncrement_le_arcLength hγac Complex.imCLM hnorm
    rwa [show Complex.imCLM (γ 1) = (γ 1).im from rfl,
      show Complex.imCLM (γ 0) = (γ 0).im from rfl, hγ1im, hγ0im] at this
  calc (1 : ℝ≥0∞)
      = ENNReal.ofReal (1 / (t - s)) * ENNReal.ofReal (t - s) := by
        rw [← ENNReal.ofReal_mul (by positivity), one_div,
          inv_mul_cancel₀ (by linarith : (t - s) ≠ 0), ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (1 / (t - s)) * ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv γ u‖₊ : ℝ≥0∞) := by
        gcongr

/-- **Modulus upper bound for the swapped rectangle.** The swapped (bottom ↔ top) family has modulus
at most `(b − a)/(t − s)`: the admissible density `(1/(t−s))·𝟙_R` has energy
`∫⁻ ρ² = area(R)/(t−s)² = (b−a)/(t−s)`. (For a *square* `b − a = t − s` this gives `≤ 1`.) -/
theorem axisRectSwap_modulus_upper_bound {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateralSwap a b s t hab hst).modulus
      ≤ ENNReal.ofReal ((b - a) / (t - s)) := by
  have hbma : (0:ℝ) < b - a := by linarith
  have htms : (0:ℝ) < t - s := by linarith
  have henergy : ∫⁻ z, ((axisRect a b s t).indicator
        (fun _ => ENNReal.ofReal (1 / (t - s))) z) ^ 2
      = ENNReal.ofReal ((b - a) / (t - s)) := by
    have hsq : (fun z => ((axisRect a b s t).indicator
          (fun _ => ENNReal.ofReal (1 / (t - s))) z) ^ 2)
        = (axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (t - s)) ^ 2) := by
      funext z; by_cases hz : z ∈ axisRect a b s t <;> simp [hz]
    rw [hsq, lintegral_indicator (measurableSet_axisRect a b s t), setLIntegral_const,
      volume_axisRect a b s t]
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_div, inv_pow]
    field_simp
  unfold Quadrilateral.modulus curveModulus
  calc ⨅ ρ ∈ {ρ : ℂ → ℝ≥0∞ | IsAdmissibleDensity ρ
          (axisRectQuadrilateralSwap a b s t hab hst).curveFamily}, ∫⁻ z, (ρ z) ^ 2
      ≤ ∫⁻ z, ((axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (t - s))) z) ^ 2 :=
        iInf₂_le ((axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (t - s))))
          (axisRectDensitySwap_admissible hab hst)
    _ = ENNReal.ofReal ((b - a) / (t - s)) := henergy

/-! ### Reduction of conjugate-image reciprocity to the per-density length–area inequality

The reciprocity `1 ≤ M(Γ) · M(Γ*)` is the infimum, over admissible density pairs `(ρ, σ)`, of the
**per-pair** length–area inequality `1 ≤ (∫∫ ρ²) · (∫∫ σ²)`. We make this reduction sound and
explicit: the `curveModulus`/`iInf` wrappers and all the `ℝ≥0∞` finiteness bookkeeping are
discharged below (an `ℝ≥0∞` lemma `one_le_biInf_mul_biInf'` plus finiteness witnesses for the two
image families via Rengel densities), leaving the *single* genuinely two-dimensional input
`imageConjugate_lengthArea_pairwise` (the per-pair inequality), which reduces to the atomic
cross-bound `imageConjugate_cross_bound` and thence to the planar Loewner residual
`loewner_image_cross_bound_axisRect` (the co-area / length–area decomposition over the image
foliation, absent from Mathlib).

Crucially, the naïve route "Cauchy–Schwarz `(∫∫ ρσ)² ≤ (∫∫ ρ²)(∫∫ σ²)` then `∫∫ ρσ ≥ 1` then `inf`
over independent `ρ, σ`" is **unsound**: `∫∫ ρσ ≥ 1` is *false* for arbitrary admissible pairs
(it holds only at the extremal pair; the perturbation `ρ = 1 + a(x)`, `σ = 1 + b(y)` with
`∫ a = ∫ b = 0` keeps `ρ, σ` admissible while making `∫∫ ρσ` drop below `1` once the perturbations
are correlated across the two constraints). The per-pair *product* inequality
`1 ≤ (∫∫ ρ²)(∫∫ σ²)` does hold for every admissible pair and is exactly equivalent (via the
infimum) to the goal, so it is the honest atomic reduction target. -/

/-- **Positive uniform separation of two disjoint nonempty compacta.** In a metric space, two
disjoint nonempty compact sets `A`, `B` are at a uniform positive distance: there is `d > 0` with
`d ≤ dist p q` for all `p ∈ A`, `q ∈ B`. The witness is `d = min over A of infDist · B`, positive
because the (closed) `B` does not meet the point of `A` realizing the minimum. -/
theorem exists_pos_setSeparation_of_disjoint_compact {α : Type*} [MetricSpace α] {A B : Set α}
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hdisj : Disjoint A B) :
    ∃ d : ℝ, 0 < d ∧ ∀ p ∈ A, ∀ q ∈ B, d ≤ dist p q := by
  have hcont : Continuous (fun p => Metric.infDist p B) := continuous_infDist_pt B
  obtain ⟨p₀, hp₀A, hp₀min⟩ := hA.exists_isMinOn hAne hcont.continuousOn
  refine ⟨Metric.infDist p₀ B, ?_, ?_⟩
  · rw [← hB.isClosed.notMem_iff_infDist_pos hBne]
    intro hp₀B; exact (hdisj.ne_of_mem hp₀A hp₀B) rfl
  · intro p hpA q hqB
    exact (hp₀min hpA).trans (Metric.infDist_le_dist_of_mem hqB)

/-- **Reduction lemma (`ℝ≥0∞` arithmetic).** If every pair `(ρ, σ)` from two index sets `I`, `J`
satisfies `1 ≤ g ρ · h σ`, the set `I` has a member with `g`-value in `(0, ∞)`, and `J` is
nonempty with a member of finite `h`-value, then `1 ≤ (⨅_{ρ∈I} g ρ) · (⨅_{σ∈J} h σ)`.

This is the sound passage from the per-pair inequality to the product of infima. The finiteness
side conditions are what rules out the degenerate `0 · ∞` failures: a finite nonzero `g ρ₀`
together with the per-pair bound forces `⨅ h > 0`, and a finite `h σ₀` bounds `⨅ h < ∞`, after
which `(⨅ h)⁻¹ ≤ ⨅ g` gives the product `≥ 1`. (All edge cases `g ρ = ∞`, `⨅ h ∈ {0, ∞}` are
handled.) -/
theorem one_le_biInf_mul_biInf' {ιS ιT : Type*} {I : Set ιS} {J : Set ιT}
    (g : ιS → ℝ≥0∞) (h : ιT → ℝ≥0∞)
    (hSfin : ∃ ρ₀ ∈ I, g ρ₀ ≠ 0 ∧ g ρ₀ ≠ ⊤)
    (hTne : J.Nonempty) (hTtop : ∃ σ₀ ∈ J, h σ₀ ≠ ⊤)
    (hpair : ∀ ρ ∈ I, g ρ ≠ ⊤ → ∀ σ ∈ J, h σ ≠ ⊤ → 1 ≤ g ρ * h σ) :
    1 ≤ (⨅ ρ ∈ I, g ρ) * (⨅ σ ∈ J, h σ) := by
  obtain ⟨ρ₀, hρ₀I, hρ₀0, hρ₀top⟩ := hSfin
  obtain ⟨σt, hσtJ, hσttop⟩ := hTtop
  obtain ⟨σn, hσnJ⟩ := hTne
  set A := ⨅ ρ ∈ I, g ρ with hAdef
  set B := ⨅ σ ∈ J, h σ with hBdef
  have hBtop : B ≠ ⊤ := ne_top_of_le_ne_top hσttop (biInf_le _ hσtJ)
  -- The pairwise bound is only assumed for finite-energy densities; for an infinite-energy `σ`
  -- (`h σ = ⊤`) the inequality `(g ·)⁻¹ ≤ h σ` is automatic, so the infimum argument is unaffected.
  have hB0 : B ≠ 0 := by
    have hle : (g ρ₀)⁻¹ ≤ B := by
      apply le_iInf₂; intro σ hσ
      rcases eq_or_ne (h σ) ⊤ with hσtop | hσtop
      · rw [hσtop]; exact le_top
      · rw [ENNReal.inv_le_iff_le_mul (fun _ => hρ₀0) (fun hh => absurd hh hρ₀top)]
        exact hpair ρ₀ hρ₀I hρ₀top σ hσ hσtop
    exact (lt_of_lt_of_le (ENNReal.inv_pos.mpr hρ₀top) hle).ne'
  have hxB : ∀ ρ ∈ I, 1 ≤ g ρ * B := by
    intro ρ hρI
    rcases eq_or_ne (g ρ) ⊤ with hgtop | hgtop
    · rw [hgtop, ENNReal.top_mul hB0]; exact le_top
    · -- `g ρ` finite: derive `g ρ ≠ 0` from the pairwise bound against the finite witness `σt`.
      have hx0 : g ρ ≠ 0 := by
        rintro hh
        have := hpair ρ hρI hgtop σt hσtJ hσttop
        rw [hh, zero_mul] at this; simp at this
      have hxinv_le : (g ρ)⁻¹ ≤ B := by
        apply le_iInf₂; intro σ hσJ
        rcases eq_or_ne (h σ) ⊤ with hσtop | hσtop
        · rw [hσtop]; exact le_top
        · rw [ENNReal.inv_le_iff_le_mul (fun _ => hx0) (fun hh => absurd hh hgtop)]
          exact hpair ρ hρI hgtop σ hσJ hσtop
      calc (1:ℝ≥0∞) = g ρ * (g ρ)⁻¹ := (ENNReal.mul_inv_cancel hx0 hgtop).symm
        _ ≤ g ρ * B := by gcongr
  have hkey : B⁻¹ ≤ A := by
    apply le_iInf₂; intro ρ hρI
    rw [ENNReal.inv_le_iff_le_mul (fun _ => hB0) (fun hh => absurd hh hBtop), mul_comm]
    exact hxB ρ hρI
  calc (1:ℝ≥0∞) = B * B⁻¹ := (ENNReal.mul_inv_cancel hB0 hBtop).symm
    _ ≤ B * A := by gcongr
    _ = A * B := mul_comm _ _

/-- **Finiteness witness for the image connecting family.** For a homeomorphism `f` and a
quadrilateral `Q` whose image region `f''Q.image` has positive (necessarily finite, by compactness)
volume and whose two image sides are disjoint, the Rengel density `(1/d)·𝟙_{f''image}` (with `d`
the positive separation of the disjoint compact image sides) is an admissible density for
`Q.imageCurveFamily f` of finite, nonzero energy `∫∫ ρ₀² = (1/d²)·volume(f''image) ∈ (0, ∞)`. (If
the image right side is empty the connecting family is empty and the unweighted indicator of
`f''image` is vacuously admissible with the same finite, nonzero energy.) -/
theorem imageCurveFamily_finiteWitness {f : ℂ → ℂ} (hf : IsHomeomorph f) (Q : Quadrilateral)
    (hposvol : 0 < volume (f '' Q.image))
    (hdisj : Disjoint (f '' Q.leftSide) (f '' Q.rightSide)) (hneL : Q.leftSide.Nonempty) :
    ∃ ρ₀ ∈ {ρ : ℂ → ℝ≥0∞ | IsAdmissibleDensity ρ (Q.imageCurveFamily f)},
      (∫⁻ z, (ρ₀ z) ^ 2) ≠ 0 ∧ (∫⁻ z, (ρ₀ z) ^ 2) ≠ ⊤ := by
  have hfc : Continuous f := hf.continuous
  have hsqcpt : IsCompact (unitSquare : Set (ℝ × ℝ)) := isCompact_Icc.prod isCompact_Icc
  have hQimgcpt : IsCompact (Q.image) := hsqcpt.image Q.continuous_toFun
  have hfQimgcpt : IsCompact (f '' Q.image) := hQimgcpt.image hfc
  have hRmeas : MeasurableSet (f '' Q.image) := hfQimgcpt.measurableSet
  have hRfin : volume (f '' Q.image) ≠ ⊤ := hfQimgcpt.measure_lt_top.ne
  have hcptL : IsCompact (Q.leftSide) := by
    unfold Quadrilateral.leftSide
    exact (isCompact_singleton.prod isCompact_Icc).image Q.continuous_toFun
  have hcptR : IsCompact (Q.rightSide) := by
    unfold Quadrilateral.rightSide
    exact (isCompact_singleton.prod isCompact_Icc).image Q.continuous_toFun
  have hcptfL : IsCompact (f '' Q.leftSide) := hcptL.image hfc
  have hcptfR : IsCompact (f '' Q.rightSide) := hcptR.image hfc
  have hnefL : (f '' Q.leftSide).Nonempty := hneL.image f
  by_cases hneR : (f '' Q.rightSide).Nonempty
  · obtain ⟨d, hd, hdist⟩ :=
      exists_pos_setSeparation_of_disjoint_compact hcptfL hcptfR hnefL hneR hdisj
    set ρ₀ : ℂ → ℝ≥0∞ := (f '' Q.image).indicator (fun _ => ENNReal.ofReal (1 / d)) with hρ₀
    have hΓ : ∀ δ ∈ Q.imageCurveFamily f, Continuous δ ∧ AbsolutelyContinuousOnInterval δ 0 1 ∧
        δ 0 ∈ f '' Q.leftSide ∧ δ 1 ∈ f '' Q.rightSide ∧
        ∀ u ∈ Set.Icc (0 : ℝ) 1, δ u ∈ f '' Q.image := fun δ hδ => hδ
    have henergy : ∫⁻ z, (ρ₀ z) ^ 2 = ENNReal.ofReal (1 / d ^ 2) * volume (f '' Q.image) := by
      have hsq : (fun z => (ρ₀ z) ^ 2)
          = (f '' Q.image).indicator (fun _ => ENNReal.ofReal (1 / d) ^ 2) := by
        funext z; rw [hρ₀]; by_cases hz : z ∈ f '' Q.image <;> simp [hz]
      have hscalar : ENNReal.ofReal (1 / d) ^ 2 = ENNReal.ofReal (1 / d ^ 2) := by
        rw [← ENNReal.ofReal_pow (by positivity), div_pow, one_pow]
      rw [hsq, lintegral_indicator hRmeas, setLIntegral_const, hscalar, mul_comm]
    refine ⟨ρ₀, rengelDensity_admissible hRmeas hd hdist hΓ, ?_, ?_⟩
    · rw [henergy]
      exact mul_ne_zero
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity) hposvol.ne'
    · rw [henergy]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRfin
  · have hempty : Q.imageCurveFamily f = ∅ := by
      ext δ; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, _, _, hδ1, _⟩; exact hneR ⟨δ 1, hδ1⟩
    set ρ₀ : ℂ → ℝ≥0∞ := (f '' Q.image).indicator (fun _ => 1) with hρ₀
    have hadm : IsAdmissibleDensity ρ₀ (Q.imageCurveFamily f) := by
      refine ⟨Measurable.indicator measurable_const hRmeas, ?_⟩
      rw [hempty]; intro δ hδ; exact absurd hδ (Set.notMem_empty δ)
    have henergy : ∫⁻ z, (ρ₀ z) ^ 2 = volume (f '' Q.image) := by
      have hsq : (fun z => (ρ₀ z) ^ 2) = (f '' Q.image).indicator (fun _ => (1:ℝ≥0∞)) := by
        funext z; rw [hρ₀]; by_cases hz : z ∈ f '' Q.image <;> simp [hz]
      rw [hsq, lintegral_indicator hRmeas, setLIntegral_const, one_mul]
    exact ⟨ρ₀, hadm, by rw [henergy]; exact hposvol.ne', by rw [henergy]; exact hRfin⟩

/-- **Positive volume of the image of an axis rectangle quadrilateral** under a homeomorphism `f`.
The open box `(a, b) × (s, t) ⊆ Q.image` maps (via the open map `f`) to a nonempty open set inside
`f''Q.image`, which therefore has positive measure. -/
theorem image_axisRectQuadrilateral_volume_pos {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    0 < volume (f '' (axisRectQuadrilateral a b s t hab hst).image) := by
  set Q := axisRectQuadrilateral a b s t hab hst
  set U : Set ℂ := {z : ℂ | (a < z.re ∧ z.re < b) ∧ (s < z.im ∧ z.im < t)} with hU
  have hUopen : IsOpen U := by
    have hUeq : U = {z : ℂ | a < z.re ∧ z.re < b} ∩ {z : ℂ | s < z.im ∧ z.im < t} := by
      ext z; simp [hU, and_assoc]
    rw [hUeq]
    exact ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const))
  have hUsub : U ⊆ Q.image := by
    rw [show Q.image = _ from axisRectQuadrilateral_image hab hst]
    rintro z ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩
  have hUne : U.Nonempty :=
    ⟨Complex.mk ((a + b) / 2) ((s + t) / 2), by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [Complex.re, Complex.im] <;> linarith⟩
  calc (0 : ℝ≥0∞) < volume (f '' U) := (hf.isOpenMap U hUopen).measure_pos _ (hUne.image f)
    _ ≤ volume (f '' Q.image) := measure_mono (Set.image_mono hUsub)

/-- The standard axis-rectangle quadrilateral's image left/right sides are disjoint under `f`, and
the left side is nonempty. The source sides lie on `{re = a}`, `{re = b}` (disjoint as `a ≠ b`); `f`
injective transports the disjointness. -/
theorem image_axisRectQuadrilateral_sides_disjoint {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    Disjoint (f '' (axisRectQuadrilateral a b s t hab hst).leftSide)
        (f '' (axisRectQuadrilateral a b s t hab hst).rightSide) ∧
      (axisRectQuadrilateral a b s t hab hst).leftSide.Nonempty := by
  set Q := axisRectQuadrilateral a b s t hab hst
  have hdisjsrc : Disjoint Q.leftSide Q.rightSide := by
    rw [show Q.leftSide = _ from axisRectQuadrilateral_leftSide hab hst,
      show Q.rightSide = _ from axisRectQuadrilateral_rightSide hab hst, Set.disjoint_left]
    rintro z ⟨hzre, _⟩ ⟨hzre', _⟩; rw [hzre] at hzre'; exact absurd hzre' (by linarith)
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro p ⟨zl, hzlL, rfl⟩ ⟨zr, hzrR, hpr⟩
    have hzz : zl = zr := hf.injective hpr.symm
    subst hzz; exact (Set.disjoint_left.mp hdisjsrc hzlL) hzrR
  · rw [show Q.leftSide = _ from axisRectQuadrilateral_leftSide hab hst]
    exact ⟨Complex.mk a s, rfl, le_refl s, hst.le⟩

/-- The swapped axis-rectangle quadrilateral's image left/right sides (bottom `{im = s}`, top
`{im = t}`) are disjoint under `f`, and the left side is nonempty. -/
theorem image_axisRectQuadrilateralSwap_sides_disjoint {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    Disjoint (f '' (axisRectQuadrilateralSwap a b s t hab hst).leftSide)
        (f '' (axisRectQuadrilateralSwap a b s t hab hst).rightSide) ∧
      (axisRectQuadrilateralSwap a b s t hab hst).leftSide.Nonempty := by
  set Q := axisRectQuadrilateralSwap a b s t hab hst
  have hdisjsrc : Disjoint Q.leftSide Q.rightSide := by
    rw [show Q.leftSide = _ from axisRectQuadrilateralSwap_leftSide hab hst,
      show Q.rightSide = _ from axisRectQuadrilateralSwap_rightSide hab hst, Set.disjoint_left]
    rintro z ⟨hzim, _⟩ ⟨hzim', _⟩; rw [hzim] at hzim'; exact absurd hzim' (by linarith)
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro p ⟨zl, hzlL, rfl⟩ ⟨zr, hzrR, hpr⟩
    have hzz : zl = zr := hf.injective hpr.symm
    subst hzz; exact (Set.disjoint_left.mp hdisjsrc hzlL) hzrR
  · rw [show Q.leftSide = _ from axisRectQuadrilateralSwap_leftSide hab hst]
    exact ⟨Complex.mk a s, rfl, le_refl a, hab.le⟩

/-- **Cauchy–Schwarz reduction (`ℝ≥0∞` arithmetic).** If the cross integral of two measurable
densities dominates `1`, i.e. `1 ≤ ∫⁻ z, ρ z · σ z`, then the product of the two energies dominates
`1`: `1 ≤ (∫∫ ρ²) · (∫∫ σ²)`.

This is the *final* sound step of the ρ-potential / co-area route to
`imageConjugate_lengthArea_pairwise`: it consumes the (genuinely hard, co-area-supplied) lower bound
`∫∫ ρσ ≥ 1` and discharges the rest by the Hölder/Cauchy–Schwarz inequality
`ENNReal.lintegral_mul_le_Lp_mul_Lq` at the conjugate exponents `(2, 2)`, then squaring.

It is **not** itself the residual: the hypothesis `1 ≤ ∫∫ ρσ` is *false* for arbitrary admissible
pairs (it holds only when `ρ, σ` are related through the extremal foliation — see the docstring of
`imageConjugate_lengthArea_pairwise`), so this lemma is stated as an *implication* and must be fed
the cross bound by the co-area argument. As a pure `ℝ≥0∞` inequality it is unconditionally true and
axiom-clean; it isolates the only part of the classical Cauchy–Schwarz route that *is* sound. -/
theorem one_le_energy_mul_energy_of_one_le_lintegral_mul {ρ σ : ℂ → ℝ≥0∞}
    (hρm : Measurable ρ) (hσm : Measurable σ)
    (hcross : 1 ≤ ∫⁻ z, ρ z * σ z) :
    1 ≤ (∫⁻ z, (ρ z) ^ 2) * (∫⁻ z, (σ z) ^ 2) := by
  set A : ℝ≥0∞ := ∫⁻ z, (ρ z) ^ 2 with hA
  set B : ℝ≥0∞ := ∫⁻ z, (σ z) ^ 2 with hB
  -- Hölder at the conjugate exponents `(2, 2)`: `∫⁻ ρσ ≤ (∫⁻ ρ^(2:ℝ))^(1/2) · (∫⁻ σ^(2:ℝ))^(1/2)`.
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℂ)
    (Real.HolderConjugate.two_two) (f := ρ) (g := σ) hρm.aemeasurable hσm.aemeasurable
  -- Identify the `rpow`-`2` energies with the `npow`-`2` energies appearing in the goal.
  have hAeq : (∫⁻ z, (ρ z) ^ (2 : ℝ)) = A := by
    rw [hA]; exact lintegral_congr fun z => ENNReal.rpow_two _
  have hBeq : (∫⁻ z, (σ z) ^ (2 : ℝ)) = B := by
    rw [hB]; exact lintegral_congr fun z => ENNReal.rpow_two _
  -- so `1 ≤ ∫⁻ ρσ ≤ A^(1/2) · B^(1/2)`.
  have hmul : (fun z => (ρ * σ) z) = fun z => ρ z * σ z := rfl
  rw [hmul, hAeq, hBeq] at hCS
  have h1le : (1 : ℝ≥0∞) ≤ A ^ (1 / (2:ℝ)) * B ^ (1 / (2:ℝ)) := le_trans hcross hCS
  -- Square: `1 = 1^(2:ℝ) ≤ (A^(1/2) · B^(1/2))^(2:ℝ) = A · B`.
  have hsq : (A ^ (1 / (2:ℝ)) * B ^ (1 / (2:ℝ))) ^ (2 : ℝ) = A * B := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    norm_num
  calc (1 : ℝ≥0∞) = (1 : ℝ≥0∞) ^ (2 : ℝ) := by rw [ENNReal.one_rpow]
    _ ≤ (A ^ (1 / (2:ℝ)) * B ^ (1 / (2:ℝ))) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h1le (by norm_num)
    _ = A * B := hsq

/-! ### Reusable Hausdorff / co-area primitives

The geodesic ρ-potential route to the cross-bound `1 ≤ ∫∫ ρσ` was retired (its sharp eikonal
`‖∇u‖ ≤ ρ` is false for finite-energy `ρ` — planar Kakeya/Nikodym; see
`imageConjugate_lengthArea_pairwise`).  The Hausdorff-measure / projection / packing lemmas below
are kept as reusable primitives for the correct crossing-principle reciprocity proof. -/

open NoWanderingDomains.Coarea in
/-- **Projection lower bound for the 1-dimensional Hausdorff measure.** If the real projection of a
planar set `S` covers an interval `[α, β]`, then `μH[1] S ≥ β − α`. The real part is `1`-Lipschitz,
so it cannot increase `μH[1]`, while `μH[1]` on the line is Lebesgue measure. This is the
quantitative core of every level-set separation lower bound: a separating set whose projection
spans `[α, β]` carries at least `β − α` of `μH[1]`-length. -/
theorem ofReal_sub_le_hausdorffMeasure_one_of_reCLM_image
    {S : Set ℂ} {α β : ℝ} (hsub : Set.Icc α β ⊆ Complex.reCLM '' S) :
    ENNReal.ofReal (β - α) ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) S := by
  have hlip : LipschitzWith 1 (Complex.reCLM : ℂ → ℝ) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Complex.reCLM_apply, NNReal.coe_one, one_mul, Real.dist_eq, ← Complex.sub_re]
    rw [dist_eq_norm]
    exact Complex.abs_re_le_norm _
  have h1 : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Complex.reCLM '' S)
      ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) S := by
    simpa [ENNReal.one_rpow] using hlip.hausdorffMeasure_image_le (d := 1) (by norm_num) S
  have h2 : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Set.Icc α β)
      ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Complex.reCLM '' S) :=
    measure_mono hsub
  have h3 : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Set.Icc α β)
      = ENNReal.ofReal (β - α) := by
    rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
  rw [h3] at h2
  exact h2.trans h1

/-- **Projection lower bound for the 1-dimensional Hausdorff measure (imaginary projection).** The
imaginary-part twin of `ofReal_sub_le_hausdorffMeasure_one_of_reCLM_image`: if the imaginary
projection of a planar set `S` covers an interval `[α, β]`, then `μH[1] S ≥ β − α`. The imaginary
part is `1`-Lipschitz, so it cannot increase `μH[1]`, while `μH[1]` on the line is Lebesgue
measure. -/
theorem ofReal_sub_le_hausdorffMeasure_one_of_imCLM_image
    {S : Set ℂ} {α β : ℝ} (hsub : Set.Icc α β ⊆ Complex.imCLM '' S) :
    ENNReal.ofReal (β - α) ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) S := by
  have hlip : LipschitzWith 1 (Complex.imCLM : ℂ → ℝ) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Complex.imCLM_apply, NNReal.coe_one, one_mul, Real.dist_eq, ← Complex.sub_im]
    rw [dist_eq_norm]
    exact Complex.abs_im_le_norm _
  have h1 : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Complex.imCLM '' S)
      ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) S := by
    simpa [ENNReal.one_rpow] using hlip.hausdorffMeasure_image_le (d := 1) (by norm_num) S
  have h2 : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Set.Icc α β)
      ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Complex.imCLM '' S) :=
    measure_mono hsub
  have h3 : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Set.Icc α β)
      = ENNReal.ofReal (β - α) := by
    rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
  rw [h3] at h2
  exact h2.trans h1

/-- **McShane / nonlinear Hahn–Banach extension of a real Lipschitz-on-`s` function.** Any function
`v : ℂ → ℝ` that is `K`-Lipschitz on a set `s` extends to a globally `K`-Lipschitz function `u` on
all of `ℂ` agreeing with `v` on `s`. This is the real-valued McShane extension, packaged as a clean
leaf for the potential construction. -/
theorem exists_lipschitzWith_extend {v : ℂ → ℝ} {s : Set ℂ} {K : ℝ≥0}
    (hv : LipschitzOnWith K v s) :
    ∃ u : ℂ → ℝ, LipschitzWith K u ∧ Set.EqOn v u s :=
  hv.extend_real




/-! ### Reusable measure-theory / path-algebra primitives

Generic helpers for absolutely-continuous curves: disjoint-interval combinatorics under monotone
reparametrization, affine change-of-variables for arc-length integrals, and the path-algebra
(`segPath`, `glueCurve`, `reversePath`).  Kept as reusable primitives for the crossing-principle
reciprocity build. -/

/-- **A monotone map preserves pairwise disjointness of `uIoc` intervals.** If the intervals
`uIoc (I i).1 (I i).2`, `i < n`, are pairwise disjoint and `φ` is monotone, then so are the
intervals `uIoc (φ (I i).1) (φ (I i).2)`, `i < n`. This is the combinatorial core needed to split
an absolutely-continuous disjoint family across a midpoint by clipping its endpoints. -/
theorem pairwiseDisjoint_uIoc_comp_monotone {φ : ℝ → ℝ} (hφ : Monotone φ)
    {n : ℕ} {I : ℕ → ℝ × ℝ}
    (hI : Set.PairwiseDisjoint (Finset.range n) (fun i => Set.uIoc (I i).1 (I i).2)) :
    Set.PairwiseDisjoint (Finset.range n)
      (fun i => Set.uIoc (φ (I i).1) (φ (I i).2)) := by
  intro i hi j hj hij
  have hdisj := hI hi hj hij
  -- Translate `Disjoint` of `uIoc` into the `min/max ≤` criterion, push `φ` through.
  simp only [Function.onFun, Set.uIoc, Set.disjoint_iff_inter_eq_empty] at hdisj ⊢
  rw [← Set.disjoint_iff_inter_eq_empty, Set.Ioc_disjoint_Ioc] at hdisj ⊢
  -- `min/max` of `φ`-values equal `φ` of `min/max` by monotonicity.
  rw [← hφ.map_min, ← hφ.map_min, ← hφ.map_max, ← hφ.map_max,
    ← hφ.map_max, ← hφ.map_min]
  exact hφ hdisj

/-- **Absolute continuity is preserved by composing on the left with a function that is Lipschitz
on a set containing the image.** If `l` is `K`-Lipschitz on `S`, `F` is absolutely continuous on
`uIcc a b`, and `F` maps `uIcc a b` into `S`, then `l ∘ F` is absolutely continuous on `uIcc a b`.
This is the `LipschitzOnWith` upgrade of the repository's `LipschitzWith`-composition pattern. -/
theorem absolutelyContinuousOnInterval_comp_lipschitzOnWith
    {Y : Type*} [PseudoMetricSpace Y] {l : ℂ → Y} {K : NNReal} {S : Set ℂ}
    (hl : LipschitzOnWith K l S) {F : ℝ → ℂ} {a b : ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b)
    (hmaps : ∀ t ∈ Set.uIcc a b, F t ∈ S) :
    AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hF ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have key := hδ' E hE hlen
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  -- Each endpoint of the disjoint family lies in `uIcc a b`, hence its `F`-image lies in `S`.
  have hmem : ∀ i ∈ Finset.range E.1,
      F (E.2 i).1 ∈ S ∧ F (E.2 i).2 ∈ S := by
    intro i hi
    exact ⟨hmaps _ (hE.1 i hi).1, hmaps _ (hE.1 i hi).2⟩
  calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
      ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
        Finset.sum_le_sum (fun i hi => by
          have hd := hl.dist_le_mul _ (hmem i hi).1 _ (hmem i hi).2
          exact hd)
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
        rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
    _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]

/-- **Two-piece concatenation of absolute continuity.** If `a ≤ m ≤ b` and `f` is absolutely
continuous on `[a, m]` and on `[m, b]`, then `f` is absolutely continuous on `[a, b]`. This is the
genuinely-missing finite-cover concatenation: a disjoint family of intervals inside `[a, b]` is
split at `m` by clipping each endpoint with `min m ·` (landing in `[a, m]`) and `max m ·` (landing
in `[m, b]`); clipping is `1`-Lipschitz and monotone, so the two clipped families are disjoint, of
total length no larger than the original, and the chord through `f m` dominates the original chord
by the triangle inequality. -/
theorem absolutelyContinuousOnInterval_concat {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {a m b : ℝ}
    (ham : a ≤ m) (hmb : m ≤ b)
    (hL : AbsolutelyContinuousOnInterval f a m)
    (hR : AbsolutelyContinuousOnInterval f m b) :
    AbsolutelyContinuousOnInterval f a b := by
  have hab : a ≤ b := le_trans ham hmb
  rw [absolutelyContinuousOnInterval_iff] at hL hR ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hL (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := hR (ε / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun E hE hlen => ?_⟩
  obtain ⟨n, I⟩ := E
  -- Clip maps: `min m ·` retracts `[a, b]` onto `[a, m]`; `max m ·` onto `[m, b]`.
  have hMinMono : Monotone (fun x : ℝ => min m x) := fun _ _ h => min_le_min le_rfl h
  have hMaxMono : Monotone (fun x : ℝ => max m x) := fun _ _ h => max_le_max le_rfl h
  -- Endpoints of `E` lie in `[a, b]`.
  have hEmem : ∀ i ∈ Finset.range n, (I i).1 ∈ Set.Icc a b ∧ (I i).2 ∈ Set.Icc a b := by
    intro i hi
    have h := hE.1 i hi
    rw [Set.uIcc_of_le hab] at h
    exact h
  -- The left-clipped family.
  set IL : ℕ → ℝ × ℝ := fun i => (min m (I i).1, min m (I i).2) with hIL
  set IR : ℕ → ℝ × ℝ := fun i => (max m (I i).1, max m (I i).2) with hIR
  -- Membership of clipped endpoints in the sub-intervals.
  have hmemL : ∀ i ∈ Finset.range n,
      min m (I i).1 ∈ Set.uIcc a m ∧ min m (I i).2 ∈ Set.uIcc a m := by
    intro i hi
    obtain ⟨⟨hi1a, hi1b⟩, ⟨hi2a, hi2b⟩⟩ := hEmem i hi
    rw [Set.uIcc_of_le ham]
    exact ⟨⟨le_min ham hi1a, min_le_left _ _⟩, ⟨le_min ham hi2a, min_le_left _ _⟩⟩
  have hmemR : ∀ i ∈ Finset.range n,
      max m (I i).1 ∈ Set.uIcc m b ∧ max m (I i).2 ∈ Set.uIcc m b := by
    intro i hi
    obtain ⟨⟨hi1a, hi1b⟩, ⟨hi2a, hi2b⟩⟩ := hEmem i hi
    rw [Set.uIcc_of_le hmb]
    exact ⟨⟨le_max_left _ _, max_le hmb hi1b⟩, ⟨le_max_left _ _, max_le hmb hi2b⟩⟩
  -- Disjointness of clipped families (monotone images of disjoint `uIoc`).
  have hdisjL : Set.PairwiseDisjoint (Finset.range n)
      (fun i => Set.uIoc (IL i).1 (IL i).2) :=
    pairwiseDisjoint_uIoc_comp_monotone hMinMono hE.2
  have hdisjR : Set.PairwiseDisjoint (Finset.range n)
      (fun i => Set.uIoc (IR i).1 (IR i).2) :=
    pairwiseDisjoint_uIoc_comp_monotone hMaxMono hE.2
  have hEL : ((n, IL) : ℕ × (ℕ → ℝ × ℝ)) ∈
      AbsolutelyContinuousOnInterval.disjWithin a m := ⟨hmemL, hdisjL⟩
  have hER : ((n, IR) : ℕ × (ℕ → ℝ × ℝ)) ∈
      AbsolutelyContinuousOnInterval.disjWithin m b := ⟨hmemR, hdisjR⟩
  -- Total lengths of clipped families do not exceed the original total length.
  -- Clipping is `1`-Lipschitz, so per-interval clipped length ≤ original length.
  have hMinLip : LipschitzWith 1 (fun x : ℝ => min m x) := LipschitzWith.id.const_min m
  have hMaxLip : LipschitzWith 1 (fun x : ℝ => max m x) := LipschitzWith.id.const_max m
  have hlenL : ∑ i ∈ Finset.range n, dist (IL i).1 (IL i).2 ≤
      ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := by
    apply Finset.sum_le_sum
    intro i _
    have := hMinLip.dist_le_mul (I i).1 (I i).2
    simpa only [hIL, NNReal.coe_one, one_mul] using this
  have hlenR : ∑ i ∈ Finset.range n, dist (IR i).1 (IR i).2 ≤
      ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := by
    apply Finset.sum_le_sum
    intro i _
    have := hMaxLip.dist_le_mul (I i).1 (I i).2
    simpa only [hIR, NNReal.coe_one, one_mul] using this
  -- Per-interval chord domination: the original chord splits through `f m`.
  have hchord : ∀ i ∈ Finset.range n,
      dist (f (I i).1) (f (I i).2) ≤
        dist (f (IL i).1) (f (IL i).2) + dist (f (IR i).1) (f (IR i).2) := by
    intro i _
    simp only [hIL, hIR]
    set u := (I i).1
    set v := (I i).2
    rcases le_total u m with h1 | h1 <;> rcases le_total v m with h2 | h2
    · -- both ≤ m : right chord collapses to `dist (f m) (f m) = 0`.
      rw [min_eq_right h1, min_eq_right h2, max_eq_left h1, max_eq_left h2, dist_self, add_zero]
    · -- u ≤ m ≤ v : split through `f m`.
      rw [min_eq_right h1, min_eq_left h2, max_eq_left h1, max_eq_right h2]
      exact dist_triangle (f u) (f m) (f v)
    · -- v ≤ m ≤ u : split through `f m`.
      rw [min_eq_left h1, min_eq_right h2, max_eq_right h1, max_eq_left h2]
      calc dist (f u) (f v) ≤ dist (f u) (f m) + dist (f m) (f v) := dist_triangle _ _ _
        _ = dist (f m) (f v) + dist (f u) (f m) := by rw [add_comm]
    · -- both ≥ m : left chord collapses to `dist (f m) (f m) = 0`.
      rw [min_eq_left h1, min_eq_left h2, max_eq_right h1, max_eq_right h2, dist_self, zero_add]
  -- Apply per-side AC bounds.
  have hltL : ∑ i ∈ Finset.range n, dist (IL i).1 (IL i).2 < δ₁ :=
    lt_of_le_of_lt hlenL (lt_of_lt_of_le hlen (min_le_left _ _))
  have hltR : ∑ i ∈ Finset.range n, dist (IR i).1 (IR i).2 < δ₂ :=
    lt_of_le_of_lt hlenR (lt_of_lt_of_le hlen (min_le_right _ _))
  have hsumL := hδ₁' (n, IL) hEL hltL
  have hsumR := hδ₂' (n, IR) hER hltR
  calc ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2)
      ≤ ∑ i ∈ Finset.range n,
          (dist (f (IL i).1) (f (IL i).2) + dist (f (IR i).1) (f (IR i).2)) :=
        Finset.sum_le_sum hchord
    _ = (∑ i ∈ Finset.range n, dist (f (IL i).1) (f (IL i).2)) +
          ∑ i ∈ Finset.range n, dist (f (IR i).1) (f (IR i).2) := by
        rw [Finset.sum_add_distrib]
    _ < ε / 2 + ε / 2 := add_lt_add hsumL hsumR
    _ = ε := by ring

/-! ### Path-concatenation and affine-reparametrization machinery (reusable, axiom-clean)

Arc-length-additive gluing of absolutely-continuous curves (`glueCurve`), affine `lintegral`
change-of-variables, and the straight-segment / reversal path-algebra.  Kept as reusable primitives
for the crossing-principle reciprocity build. -/

/-- **Affine `lintegral` substitution on an interval.** For `c > 0`,
`∫⁻ t in Icc p q, G(c t + d) = c⁻¹ · ∫⁻ s in Icc (c p + d) (c q + d), G s`. The change of variables
`s = c t + d` (translation + scaling, both measure-(quasi)preserving) via `setLIntegral_map`. -/
theorem lintegral_Icc_comp_affine {c d : ℝ} (hc : 0 < c) (p q : ℝ) (G : ℝ → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ t in Set.Icc p q, G (c * t + d)
      = ENNReal.ofReal c⁻¹ * ∫⁻ s in Set.Icc (c * p + d) (c * q + d), G s := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hmeas : Measurable (fun t : ℝ => c * t + d) := (measurable_const_mul c).add_const d
  have hpre : (fun t : ℝ => c * t + d) ⁻¹' Set.Icc (c * p + d) (c * q + d) = Set.Icc p q := by
    ext t; simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
  have hkey := setLIntegral_map (μ := volume) (f := G) (g := fun t : ℝ => c * t + d)
    (s := Set.Icc (c * p + d) (c * q + d)) measurableSet_Icc hG hmeas
  have hmapeq : Measure.map (fun t : ℝ => c * t + d) volume
      = ENNReal.ofReal |c⁻¹| • (volume : Measure ℝ) := by
    rw [show (fun t : ℝ => c * t + d) = (fun s => d + s) ∘ (fun t => c * t) by
      funext t; simp [add_comm],
      ← Measure.map_map (measurable_const_add d) (measurable_const_mul c)]
    rw [Real.map_volume_mul_left hcne, Measure.map_smul, map_add_left_eq_self]
  rw [hmapeq, hpre, setLIntegral_smul_measure, abs_of_pos (inv_pos.mpr hc)] at hkey
  exact hkey.symm

/-- **An affine map sends planar-null sets to null preimages.** For `c ≠ 0`, the preimage of a
null set `N ⊆ ℝ` under `t ↦ c t + d` is null. (Decompose into translation, then scaling.) -/
theorem affine_preimage_null {c d : ℝ} (hc : c ≠ 0) {N : Set ℝ} (hN : volume N = 0) :
    volume ((fun t : ℝ => c * t + d) ⁻¹' N) = 0 := by
  have hdecomp : (fun t : ℝ => c * t + d) ⁻¹' N
      = (fun t : ℝ => c * t) ⁻¹' ((fun s => d + s) ⁻¹' N) := by
    ext t; simp [Set.mem_preimage, add_comm]
  rw [hdecomp]
  have h1 : volume ((fun s : ℝ => d + s) ⁻¹' N) = 0 := by rw [measure_preimage_add]; exact hN
  rw [Real.volume_preimage_mul_left hc, h1, mul_zero]

/-- **A.e. differentiability transfers along an affine reparametrization.** If `δ` is absolutely
continuous on `[0, 1]` (hence differentiable a.e.) and `t ↦ c t + d` maps `Ioo p q` into `Ioo 0 1`
(with `c > 0`), then `δ` is differentiable at `c t + d` for a.e. `t ∈ Ioo p q`. -/
theorem ae_diff_comp_affine {δ : ℝ → ℂ} (hδac : AbsolutelyContinuousOnInterval δ 0 1)
    {c d : ℝ} (hc : 0 < c) (p q : ℝ)
    (hmaps : ∀ t ∈ Set.Ioo p q, c * t + d ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioo p q)), DifferentiableAt ℝ δ (c * t + d) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hδdiff : ∀ᵐ s : ℝ, s ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ δ s :=
    hδac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  set BadS : Set ℝ := {s | s ∈ Set.uIcc (0:ℝ) 1 ∧ ¬ DifferentiableAt ℝ δ s} with hBadS
  have hBadS_null : volume BadS = 0 := by
    rw [ae_iff] at hδdiff; refine measure_mono_null (fun s hs => ?_) hδdiff
    exact fun himp => hs.2 (himp hs.1)
  have hpre_null := affine_preimage_null hcne hBadS_null (d := d)
  rw [ae_restrict_iff' measurableSet_Ioo, ae_iff]
  refine measure_mono_null (fun t ht => ?_) hpre_null
  have htIoo : t ∈ Set.Ioo p q := by by_contra h; exact ht (fun hh => absurd hh h)
  have htbad : ¬ DifferentiableAt ℝ δ (c * t + d) := fun hh => ht (fun _ => hh)
  exact ⟨Set.mem_uIcc.mpr (Or.inl ⟨(hmaps t htIoo).1.le, (hmaps t htIoo).2.le⟩), htbad⟩

/-- **Affine reparametrization preserves the ρ-arc-length integrand (open-interval form).** With
`c > 0` and the affine substitution `s = c t + d` mapping `Ioo p q → Ioo 0 1`, the chain-rule factor
`c` exactly cancels the substitution Jacobian `c⁻¹`. -/
theorem arcLength_comp_affine_Ioo (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ) {δ : ℝ → ℂ}
    (hδac : AbsolutelyContinuousOnInterval δ 0 1) (hδcont : Continuous δ)
    {c d : ℝ} (hc : 0 < c) (p q : ℝ)
    (hmaps : ∀ t ∈ Set.Ioo p q, c * t + d ∈ Set.Ioo (0 : ℝ) 1) :
    ∫⁻ t in Set.Ioo p q, ρ (δ (c * t + d)) * (‖deriv (fun t => δ (c * t + d)) t‖₊ : ℝ≥0∞)
      = ∫⁻ s in Set.Ioo (c * p + d) (c * q + d), ρ (δ s) * (‖deriv δ s‖₊ : ℝ≥0∞) := by
  have hchain : (fun t => ρ (δ (c * t + d)) * (‖deriv (fun t => δ (c * t + d)) t‖₊ : ℝ≥0∞))
      =ᶠ[ae (volume.restrict (Set.Ioo p q))]
      (fun t => ENNReal.ofReal c * (ρ (δ (c * t + d)) * (‖deriv δ (c * t + d)‖₊ : ℝ≥0∞))) := by
    filter_upwards [ae_diff_comp_affine hδac hc p q hmaps] with t htd
    have haff : HasDerivAt (fun t : ℝ => c * t + d) c t := by
      simpa using ((hasDerivAt_id t).const_mul c).add_const d
    have hderiv : deriv (fun t => δ (c * t + d)) t = c • deriv δ (c * t + d) := by
      have := (htd.hasDerivAt.scomp t haff); simpa [Function.comp] using! this.deriv
    rw [hderiv]
    have hnorm : (‖(c:ℝ) • deriv δ (c*t+d)‖₊ : ℝ≥0∞)
        = ENNReal.ofReal c * (‖deriv δ (c*t+d)‖₊ : ℝ≥0∞) := by
      rw [Complex.real_smul]
      have h1 : ‖(c:ℂ) * deriv δ (c*t+d)‖ = c * ‖deriv δ (c*t+d)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, h1, ENNReal.ofReal_mul hc.le,
        ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    rw [hnorm]; ring
  rw [lintegral_congr_ae hchain, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hIooIcc1 : ∫⁻ t in Set.Ioo p q, ρ (δ (c * t + d)) * (‖deriv δ (c*t+d)‖₊ : ℝ≥0∞)
      = ∫⁻ t in Set.Icc p q, ρ (δ (c * t + d)) * (‖deriv δ (c*t+d)‖₊ : ℝ≥0∞) :=
    setLIntegral_congr Ioo_ae_eq_Icc
  have hIooIcc2 : ∫⁻ s in Set.Ioo (c*p+d) (c*q+d), ρ (δ s) * (‖deriv δ s‖₊ : ℝ≥0∞)
      = ∫⁻ s in Set.Icc (c*p+d) (c*q+d), ρ (δ s) * (‖deriv δ s‖₊ : ℝ≥0∞) :=
    setLIntegral_congr Ioo_ae_eq_Icc
  rw [hIooIcc1, hIooIcc2]
  have hGmeas : Measurable (fun s => ρ (δ s) * (‖deriv δ s‖₊ : ℝ≥0∞)) :=
    Measurable.mul (hρ.comp hδcont.measurable) (measurable_deriv δ).nnnorm.coe_nnreal_ennreal
  have hsub := lintegral_Icc_comp_affine (d := d) hc p q
    (fun s => ρ (δ s) * (‖deriv δ s‖₊ : ℝ≥0∞)) hGmeas
  rw [hsub, ← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ (ne_of_gt hc),
    ENNReal.ofReal_one, one_mul]

/-- **Absolute continuity transfers along an affine reparametrization.** If `δ` is AC on
`[c p + d, c q + d]` (`c > 0`), then `t ↦ δ(c t + d)` is AC on `[p, q]`. The affine map is monotone
Lipschitz, so it sends a disjoint family in `[p, q]` to a disjoint family in `[c p + d, c q + d]`
with lengths scaled by `c`. -/
theorem ac_comp_affine {δ : ℝ → ℂ} {c d : ℝ} (hc : 0 < c) {p q : ℝ}
    (hδ : AbsolutelyContinuousOnInterval δ (c * p + d) (c * q + d)) :
    AbsolutelyContinuousOnInterval (fun t => δ (c * t + d)) p q := by
  rw [absolutelyContinuousOnInterval_iff] at hδ ⊢
  intro ε hε
  obtain ⟨D, hD, hD'⟩ := hδ ε hε
  refine ⟨D / c, by positivity, fun E hE hlen => ?_⟩
  set aff : ℝ → ℝ := fun x => c * x + d with haff
  have hmono : Monotone aff := fun x y hxy => by simp only [haff]; nlinarith
  set IL : ℕ → ℝ × ℝ := fun i => (aff (E.2 i).1, aff (E.2 i).2) with hIL
  have hEmem : ((E.1, IL) : ℕ × (ℕ → ℝ × ℝ)) ∈
      AbsolutelyContinuousOnInterval.disjWithin (c*p+d) (c*q+d) := by
    refine ⟨fun i hi => ?_, ?_⟩
    · have h := hE.1 i hi
      have hmaps : ∀ x ∈ Set.uIcc p q, aff x ∈ Set.uIcc (c*p+d) (c*q+d) := by
        intro x hx
        rw [Set.mem_uIcc] at hx ⊢
        rcases hx with hx | hx
        · refine Or.inl ⟨?_, ?_⟩ <;>
            (simp only [haff]; nlinarith [hx.1])
        · refine Or.inr ⟨?_, ?_⟩ <;>
            (simp only [haff]; nlinarith [hx.1])
      exact ⟨hmaps _ h.1, hmaps _ h.2⟩
    · exact pairwiseDisjoint_uIoc_comp_monotone hmono hE.2
  have hlenscale : ∑ i ∈ Finset.range E.1, dist (IL i).1 (IL i).2
      = c * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hIL, haff, Real.dist_eq]
    rw [show c * (E.2 i).1 + d - (c * (E.2 i).2 + d) = c * ((E.2 i).1 - (E.2 i).2) by ring,
      abs_mul, abs_of_pos hc]
  have hlen' : ∑ i ∈ Finset.range E.1, dist (IL i).1 (IL i).2 < D := by
    rw [hlenscale]
    calc c * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2
        < c * (D / c) := mul_lt_mul_of_pos_left hlen hc
      _ = D := by field_simp
  have hkey := hD' (E.1, IL) hEmem hlen'
  convert hkey using 1

/-- **Absolute continuity is determined by the values on the interval.** If `f = g` on `uIcc a b`,
then `f` AC on `[a, b]` implies `g` AC on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_congr {f g : ℝ → ℂ} {a b : ℝ}
    (h : Set.EqOn f g (Set.uIcc a b)) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨d, hd, hd'⟩ := hf ε hε
  refine ⟨d, hd, fun E hE hlen => ?_⟩
  have hkey := hd' E hE hlen
  have heq : ∀ i ∈ Finset.range E.1,
      dist (g (E.2 i).1) (g (E.2 i).2) = dist (f (E.2 i).1) (f (E.2 i).2) := by
    intro i hi; rw [← h (hE.1 i hi).1, ← h (hE.1 i hi).2]
  rw [Finset.sum_congr rfl heq]; exact hkey

/-! #### The straight segment path and the geodesic glue -/

/-- The straight segment `t ↦ z + t (y − z)` from `z` to `y`, parametrized affinely on `[0, 1]`. -/
noncomputable def segPath (z y : ℂ) : ℝ → ℂ := fun t => z + (t : ℂ) * (y - z)

/-- The straight segment starts at `z`: `segPath z y 0 = z`. -/
theorem segPath_zero (z y : ℂ) : segPath z y 0 = z := by simp [segPath]
/-- The straight segment ends at `y`: `segPath z y 1 = y`. -/
theorem segPath_one (z y : ℂ) : segPath z y 1 = y := by simp [segPath]

/-- The straight segment has constant derivative `y − z` at every point. -/
theorem segPath_hasDerivAt (z y : ℂ) (t : ℝ) : HasDerivAt (segPath z y) (y - z) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (y - z)) (y - z) t := by
    have : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) t := by
      simpa using! (Complex.ofRealCLM.hasDerivAt (x := t))
    simpa using this.mul_const (y - z)
  have h2 : HasDerivAt (fun t : ℝ => z + (t : ℂ) * (y - z)) (y - z) t := by
    have := (hasDerivAt_const t z).add h1; rwa [zero_add] at this
  exact h2

/-- The derivative of the straight segment is the constant `y − z`. -/
theorem segPath_deriv (z y : ℂ) (t : ℝ) : deriv (segPath z y) t = y - z :=
  (segPath_hasDerivAt z y t).deriv

/-- The straight segment is continuous. -/
theorem segPath_continuous (z y : ℂ) : Continuous (segPath z y) := by
  unfold segPath
  exact continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)

/-- The straight segment is `‖y − z‖`-Lipschitz. -/
theorem segPath_lipschitz (z y : ℂ) :
    LipschitzWith (Real.toNNReal ‖y - z‖) (segPath z y) := by
  refine LipschitzWith.of_dist_le_mul (fun t₁ t₂ => ?_)
  unfold segPath
  rw [Complex.dist_eq]
  have : (z + (t₁ : ℂ) * (y - z)) - (z + (t₂ : ℂ) * (y - z))
      = ((t₁ - t₂ : ℝ) : ℂ) * (y - z) := by push_cast; ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.coe_toNNReal _ (norm_nonneg _), Real.dist_eq, mul_comm]

/-- The straight segment is absolutely continuous on `[0, 1]`. -/
theorem segPath_ac (z y : ℂ) : AbsolutelyContinuousOnInterval (segPath z y) 0 1 :=
  ((segPath_lipschitz z y).lipschitzOnWith).absolutelyContinuousOnInterval

/-- The ρ-arc-length of the straight segment `[z, y]` is `∫₀¹ ρ(z + t(y−z)) · ‖y − z‖ dt`. -/
theorem arcLengthLineIntegral_segPath (ρ : ℂ → ℝ≥0∞) (z y : ℂ) :
    arcLengthLineIntegral ρ (segPath z y)
      = ∫⁻ t in Set.Icc (0:ℝ) 1, ρ (segPath z y t) * (‖y - z‖₊ : ℝ≥0∞) := by
  unfold arcLengthLineIntegral
  refine setLIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
  simp only [segPath_deriv]

/-- The **glue** of two curves `δ` (covering `[0, 1/2]` via `t ↦ δ(2t)`) and `δp` (covering
`[1/2, 1]` via `t ↦ δp(2t − 1)`). When `δ 1 = δp 0` this is the concatenation `δ` then `δp`,
reparametrized to `[0, 1]`. -/
noncomputable def glueCurve (δ δp : ℝ → ℂ) : ℝ → ℂ :=
  fun t => if t ≤ 1/2 then δ (2 * t) else δp (2 * t - 1)

/-- The glue of two continuous curves that match at the join (`δ 1 = δp 0`) is continuous. -/
theorem glueCurve_continuous {δ δp : ℝ → ℂ} (hδc : Continuous δ) (hδpc : Continuous δp)
    (hmatch : δ 1 = δp 0) : Continuous (glueCurve δ δp) := by
  unfold glueCurve
  refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
  · exact hδc.comp (by fun_prop)
  · exact hδpc.comp (by fun_prop)
  · intro x hx; rw [hx]; norm_num; rw [hmatch]

/-- The glued curve starts at the first piece's start: `glueCurve δ δp 0 = δ 0`. -/
theorem glueCurve_zero (δ δp : ℝ → ℂ) : glueCurve δ δp 0 = δ 0 := by simp [glueCurve]
/-- The glued curve ends at the second piece's end: `glueCurve δ δp 1 = δp 1`. -/
theorem glueCurve_one (δ δp : ℝ → ℂ) : glueCurve δ δp 1 = δp 1 := by
  simp only [glueCurve]; rw [if_neg (by norm_num)]; norm_num

/-- On the left half `[0, 1/2]` the glued curve is the reparametrized first piece `t ↦ δ (2t)`. -/
theorem glueCurve_eqOn_left (δ δp : ℝ → ℂ) :
    Set.EqOn (fun t => δ (2*t+0)) (glueCurve δ δp) (Set.uIcc 0 (1/2)) := by
  intro t ht
  rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at ht
  simp only [glueCurve, add_zero]; rw [if_pos (by linarith [ht.2])]

/-- On the right half `[1/2, 1]` the glued curve is the reparametrized second piece
`t ↦ δp (2t − 1)`. -/
theorem glueCurve_eqOn_right {δ δp : ℝ → ℂ} (hmatch : δ 1 = δp 0) :
    Set.EqOn (fun t => δp (2*t+(-1))) (glueCurve δ δp) (Set.uIcc (1/2) 1) := by
  intro t ht
  rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at ht
  simp only [glueCurve]
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h]; norm_num [← hmatch]
  · rw [if_neg (by linarith)]; ring_nf

/-- If both pieces stay in `S` on `[0, 1]`, so does the glued curve. -/
theorem glueCurve_mem {δ δp : ℝ → ℂ} {S : Set ℂ}
    (hδ : ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ S) (hδp : ∀ t ∈ Set.Icc (0 : ℝ) 1, δp t ∈ S) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, glueCurve δ δp t ∈ S := by
  intro t ht
  rw [Set.mem_Icc] at ht
  simp only [glueCurve]
  by_cases h : t ≤ 1/2
  · rw [if_pos h]; exact hδ _ (Set.mem_Icc.mpr ⟨by linarith [ht.1], by linarith⟩)
  · rw [if_neg h]; exact hδp _ (Set.mem_Icc.mpr ⟨by linarith, by linarith [ht.2]⟩)

/-- The glue of two absolutely continuous curves matching at the join is absolutely continuous
on `[0, 1]`. -/
theorem glueCurve_ac {δ δp : ℝ → ℂ}
    (hδac : AbsolutelyContinuousOnInterval δ 0 1)
    (hδpac : AbsolutelyContinuousOnInterval δp 0 1) (hmatch : δ 1 = δp 0) :
    AbsolutelyContinuousOnInterval (glueCurve δ δp) 0 1 := by
  refine absolutelyContinuousOnInterval_concat (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) ?_ ?_
  · have hpiece : AbsolutelyContinuousOnInterval (fun t => δ (2*t+0)) 0 (1/2) := by
      apply ac_comp_affine (c := 2) (d := 0) (by norm_num) (p := 0) (q := 1/2)
      have he1 : (2:ℝ)*0+0 = 0 := by norm_num
      have he2 : (2:ℝ)*(1/2)+0 = 1 := by norm_num
      rw [he1, he2]; exact hδac
    exact absolutelyContinuousOnInterval_congr (glueCurve_eqOn_left δ δp) hpiece
  · have hpiece : AbsolutelyContinuousOnInterval (fun t => δp (2*t+(-1))) (1/2) 1 := by
      apply ac_comp_affine (c := 2) (d := -1) (by norm_num) (p := 1/2) (q := 1)
      have he1 : (2:ℝ)*(1/2)+(-1) = 0 := by norm_num
      have he2 : (2:ℝ)*1+(-1) = 1 := by norm_num
      rw [he1, he2]; exact hδpac
    exact absolutelyContinuousOnInterval_congr (glueCurve_eqOn_right hmatch) hpiece

/-- **Arc-length of the glue is additive.** `arcLength(glue δ δp) = arcLength δ + arcLength δp`,
from the affine-reparametrization arc-length invariance on each half. -/
theorem arcLengthLineIntegral_glueCurve (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ) {δ δp : ℝ → ℂ}
    (hδac : AbsolutelyContinuousOnInterval δ 0 1) (hδcont : Continuous δ)
    (hδpac : AbsolutelyContinuousOnInterval δp 0 1) (hδpcont : Continuous δp) :
    arcLengthLineIntegral ρ (glueCurve δ δp)
      = arcLengthLineIntegral ρ δ + arcLengthLineIntegral ρ δp := by
  have hglue_split : arcLengthLineIntegral ρ (glueCurve δ δp)
      = (∫⁻ t in Set.Icc (0:ℝ) (1/2), ρ (glueCurve δ δp t) * (‖deriv (glueCurve δ δp) t‖₊ : ℝ≥0∞))
        + ∫⁻ t in Set.Ioc (1/2:ℝ) 1, ρ (glueCurve δ δp t)
            * (‖deriv (glueCurve δ δp) t‖₊ : ℝ≥0∞) := by
    unfold arcLengthLineIntegral
    have hun : Set.Icc (0:ℝ) 1 = Set.Icc (0:ℝ) (1/2) ∪ Set.Ioc (1/2:ℝ) 1 := by
      rw [Set.Icc_union_Ioc_eq_Icc (by norm_num) (by norm_num)]
    rw [hun, lintegral_union measurableSet_Ioc
      (Set.disjoint_left.mpr (fun x hx hx' => by
        simp only [Set.mem_Icc, Set.mem_Ioc] at hx hx'; linarith [hx.2, hx'.1]))]
  rw [hglue_split]
  congr 1
  · unfold arcLengthLineIntegral
    rw [← setLIntegral_congr Ioo_ae_eq_Icc]
    have hpt : ∀ t ∈ Set.Ioo (0:ℝ) (1/2),
        ρ (glueCurve δ δp t) * (‖deriv (glueCurve δ δp) t‖₊ : ℝ≥0∞)
          = ρ (δ (2*t+0)) * (‖deriv (fun t => δ (2*t+0)) t‖₊ : ℝ≥0∞) := by
      intro t ht
      have hval : glueCurve δ δp t = δ (2*t+0) := by
        simp only [glueCurve, add_zero]; rw [if_pos (by linarith [ht.2])]
      have hderiv : deriv (glueCurve δ δp) t = deriv (fun t => δ (2*t+0)) t := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        simp only [glueCurve, Set.mem_Ioo, add_zero] at hs ⊢; rw [if_pos hs.2.le]
      rw [hval, hderiv]
    rw [setLIntegral_congr_fun measurableSet_Ioo hpt]
    have hkey := arcLength_comp_affine_Ioo ρ hρ hδac hδcont (c := 2) (d := 0) (by norm_num) 0 (1/2)
      (fun t ht => by constructor <;> [linarith [ht.1]; (simp only [add_zero]; linarith [ht.2])])
    rw [hkey]
    have hb1 : (2:ℝ)*0+0 = 0 := by norm_num
    have hb2 : (2:ℝ)*(1/2)+0 = 1 := by norm_num
    rw [hb1, hb2, setLIntegral_congr (Ioo_ae_eq_Icc (a := (0:ℝ)) (b := 1))]
  · unfold arcLengthLineIntegral
    rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
    have hpt : ∀ t ∈ Set.Ioo (1/2:ℝ) 1,
        ρ (glueCurve δ δp t) * (‖deriv (glueCurve δ δp) t‖₊ : ℝ≥0∞)
          = ρ (δp (2*t+(-1))) * (‖deriv (fun t => δp (2*t+(-1))) t‖₊ : ℝ≥0∞) := by
      intro t ht
      have hval : glueCurve δ δp t = δp (2*t+(-1)) := by
        simp only [glueCurve]; rw [if_neg (by linarith [ht.1])]; ring_nf
      have hderiv : deriv (glueCurve δ δp) t = deriv (fun t => δp (2*t+(-1))) t := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        simp only [glueCurve, Set.mem_Ioo] at hs ⊢
        rw [if_neg (by linarith [hs.1])]; ring_nf
      rw [hval, hderiv]
    rw [setLIntegral_congr_fun measurableSet_Ioo hpt]
    have hkey := arcLength_comp_affine_Ioo ρ hρ hδpac hδpcont (c := 2) (d := -1) (by norm_num)
      (1/2) 1 (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    rw [hkey]
    have hb1 : (2:ℝ)*(1/2)+(-1) = 0 := by norm_num
    have hb2 : (2:ℝ)*1+(-1) = 1 := by norm_num
    rw [hb1, hb2, setLIntegral_congr (Ioo_ae_eq_Icc (a := (0:ℝ)) (b := 1))]




end NoWanderingDomains
