/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Modulus
import NoWanderingDomains.QC.Defs.Geometric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Ring (annulus) domains and their conformal modulus

A **ring domain** (or **ring**) is a doubly connected plane domain: a connected open set whose
complement in the Riemann sphere has exactly two components. Up to conformal equivalence a ring is
determined by a single real invariant, its **modulus**. This file sets up the ring-modulus theory
needed for the quasiconformal-regularity layer (quasisymmetry and equicontinuity of quasiconformal
families); the sharp extremal estimates live in `QC/Regularity/Grotzsch.lean` and the regularity
consequences in `QC/Regularity/Quasisymmetry.lean`.

The conformal modulus of a ring is defined here as the `curveModulus` of its **connecting curve
family** — the family of curves joining the two boundary components. (For a round annulus
`{r < |z - z₀| < R}` this `curveModulus` equals `2π / log(R/r)`; that closed form is *not* assumed
here and is part of the extremal theory.) Two canonical extremal rings are recorded:

* the **Grötzsch ring** `grotzschRing s` — the unit disk slit along the segment `[0, s]`,
  `0 < s < 1`, separating `{0} ∪ [0, s]` from the unit circle;
* the **Teichmüller ring** `teichmullerRing t` — the plane slit along `[-1, 0] ∪ [t, ∞)`,
  `t > 0`, separating `[-1, 0]` from `[t, ∞)`.

## Main definitions

* `RoundAnnulus z₀ r R` — the open round annulus `{z | r < |z - z₀| < R}`;
* `connectingCurveFamily E F U` — the absolutely continuous curves in `U` joining a curve point on
  `E` to a curve point on `F` while staying in `U`;
* `ringModulus z₀ r R` — the conformal modulus of the round annulus `RoundAnnulus z₀ r R`,
  i.e. the `curveModulus` of the family of curves connecting its two boundary circles;
* `grotzschRing s`, `teichmullerRing t` — the two canonical extremal rings;
* `grotzschModulus s`, `teichmullerModulus t` — their moduli.
-/

open MeasureTheory
open scoped ENNReal NNReal Topology Real

namespace NoWanderingDomains

/-- The open **round annulus** `{z | r < |z - z₀| < R}` centred at `z₀` with radii `r < R`. The two
boundary components are the circles of radius `r` and `R`. -/
def RoundAnnulus (z₀ : ℂ) (r R : ℝ) : Set ℂ :=
  {z | r < dist z z₀ ∧ dist z z₀ < R}

/-- The inner boundary circle `{z | |z - z₀| = r}` of the round annulus. -/
def innerCircle (z₀ : ℂ) (r : ℝ) : Set ℂ := {z | dist z z₀ = r}

/-- The outer boundary circle `{z | |z - z₀| = R}` of the round annulus. -/
def outerCircle (z₀ : ℂ) (R : ℝ) : Set ℂ := {z | dist z z₀ = R}

/-- The **connecting curve family** of a ring with boundary components `E`, `F` bounding an open
set `U`: the absolutely continuous curves that start on `E`, end on `F`, and whose interior lies in
`U`. The endpoints sit on the boundary components `E`, `F` (disjoint from the open ring `U`), while
the open part `γ '' (0, 1)` stays inside `U`; its `curveModulus` is the conformal modulus of the
ring. (Requiring `γ t ∈ U` on the closed `[0, 1]` would force the endpoints into `U`, and since
`E, F` are disjoint from the open `U` the family would be empty.) It is the analogue of
`Quadrilateral.curveFamily`, with the two opposite sides replaced by the ring's two boundary
components. -/
def connectingCurveFamily (E F U : Set ℂ) : Set (ℝ → ℂ) :=
  {γ | Continuous γ ∧ AbsolutelyContinuousOnInterval γ 0 1 ∧
    γ 0 ∈ E ∧ γ 1 ∈ F ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, γ t ∈ U}

/-- The **conformal modulus of a round annulus** `{r < |z - z₀| < R}`: the `curveModulus` of the
family of absolutely continuous curves inside the annulus joining its inner circle to its outer
circle. For a genuine round annulus this equals `2π / log (R / r)`; that value is the content of the
extremal theory and is not built into the definition. -/
noncomputable def ringModulus (z₀ : ℂ) (r R : ℝ) : ℝ≥0∞ :=
  curveModulus (connectingCurveFamily (innerCircle z₀ r) (outerCircle z₀ R) (RoundAnnulus z₀ r R))

/-- The **Grötzsch ring** `grotzschRing s` for `0 < s < 1`: the open unit disk with the closed
segment `[0, s]` on the positive real axis removed. It separates the boundary continuum
`{0} ∪ [0, s]` from the unit circle and is the extremal ring for the Grötzsch problem (the ring of
*largest* modulus among rings separating `{0, s}` from the unit circle). -/
def grotzschRing (s : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) 1 \ (segment ℝ (0 : ℂ) (s : ℂ))

/-- The **Teichmüller ring** `teichmullerRing t` for `t > 0`: the whole plane with the two segments
`[-1, 0]` and `[t, +∞)` (on the real axis) removed. It separates `[-1, 0]` from `[t, ∞)` and is the
extremal ring for the Teichmüller problem. The unbounded slit `[t, ∞)` is encoded as the set of
points `x + 0·i` with `x ≥ t`. -/
def teichmullerRing (t : ℝ) : Set ℂ :=
  Set.univ \ (segment ℝ ((-1 : ℝ) : ℂ) (0 : ℂ) ∪ {z : ℂ | z.im = 0 ∧ t ≤ z.re})

/-- The inner boundary continuum of the Grötzsch ring: the slit `[0, s]`. -/
def grotzschInner (s : ℝ) : Set ℂ := segment ℝ (0 : ℂ) (s : ℂ)

/-- The outer boundary continuum of the Grötzsch ring: the unit circle. -/
def grotzschOuter : Set ℂ := Metric.sphere (0 : ℂ) 1

/-- The **Grötzsch modulus** `grotzschModulus s`, `0 < s < 1`: the conformal modulus of the
Grötzsch ring `grotzschRing s`, i.e. the `curveModulus` of the family of absolutely continuous
curves in `grotzschRing s` joining the slit `[0, s]` to the unit circle. In this connecting-family
convention it is the reciprocal of the classical Grötzsch separating module `μ(s)` of
Lehto–Virtanen: as `s → 0` the ring approaches the punctured disk and the connecting modulus tends
to `0`; as
`s → 1` the slit fills a diameter and the connecting modulus tends to `+∞`. This is the universal
function controlling all planar quasiconformal distortion. -/
noncomputable def grotzschModulus (s : ℝ) : ℝ≥0∞ :=
  curveModulus (connectingCurveFamily (grotzschInner s) grotzschOuter (grotzschRing s))

/-- The inner boundary continuum of the Teichmüller ring: the segment `[-1, 0]`. -/
def teichmullerInner : Set ℂ := segment ℝ ((-1 : ℝ) : ℂ) (0 : ℂ)

/-- The outer boundary continuum of the Teichmüller ring: the ray `[t, ∞)` on the real axis. -/
def teichmullerOuter (t : ℝ) : Set ℂ := {z : ℂ | z.im = 0 ∧ t ≤ z.re}

/-- The **Teichmüller modulus** `teichmullerModulus t`, `t > 0`: the conformal modulus of the
Teichmüller ring `teichmullerRing t`, i.e. the `curveModulus` of the family of absolutely continuous
curves in `teichmullerRing t` joining `[-1, 0]` to `[t, ∞)`. In this connecting-family convention
the Grötzsch and Teichmüller moduli are related by the Teichmüller identity
`teichmullerModulus t = (1 / 2) · grotzschModulus (1 / √(1 + t))` (the classical separating-module
factor `2` becomes `1 / 2` under reciprocity); both are part of the extremal theory in
`Grotzsch.lean`. -/
noncomputable def teichmullerModulus (t : ℝ) : ℝ≥0∞ :=
  curveModulus (connectingCurveFamily teichmullerInner (teichmullerOuter t) (teichmullerRing t))

/-- **Monotonicity of the connecting-family modulus in the ambient ring.** Enlarging the ambient set
`U` (with the same boundary components) can only add admissible curves, so the modulus does not
decrease. A structural consequence of `curveModulus_mono`, recorded for the comparison arguments in
the extremal theory. -/
theorem ringModulus_connecting_mono {E F U₁ U₂ : Set ℂ} (hU : U₁ ⊆ U₂) :
    curveModulus (connectingCurveFamily E F U₁) ≤ curveModulus (connectingCurveFamily E F U₂) := by
  refine curveModulus_mono ?_
  rintro γ ⟨hcont, hac, h0, h1, hsub⟩
  exact ⟨hcont, hac, h0, h1, fun t ht => hU (hsub t ht)⟩

/-- **The modulus of a round annulus.** For radii `0 < r < R` the conformal modulus of the round
annulus `{r < |z - z₀| < R}` — the `curveModulus` of the family of curves joining its inner circle
to its outer circle — equals `2π / log (R / r)`. The extremal density is the radial
`ρ(z) = 1 / (|z - z₀| · log (R / r))`: it is admissible (every connecting curve sweeps the radial
range `[r, R]`, so `∫ ρ ≥ ∫_r^R ds / (s · log (R/r)) = 1`) and has energy
`∫∫ ρ² = 2π / log (R / r)`, while the length–area (Cauchy–Schwarz over radial rays) inequality shows
no admissible density has smaller energy. -/
theorem ringModulus_roundAnnulus {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ringModulus z₀ r R = ENNReal.ofReal (2 * Real.pi / Real.log (R / r)) := by
  set L := Real.log (R / r) with hL
  have hRr1 : 1 < R / r := (one_lt_div hr).mpr hrR
  have hLpos : 0 < L := Real.log_pos hRr1
  -- ===================================================================
  -- Helper 1: a Lipschitz map composed with an AC function is AC.
  -- ===================================================================
  have lipComp_ac : ∀ {Y : Type} [PseudoMetricSpace Y] {F : ℝ → ℂ} {l : ℂ → Y} {K : NNReal},
      LipschitzWith K l → ∀ {a b : ℝ}, AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
    intro Y _ F l K hl a b hF
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
  -- ===================================================================
  -- Helper 2: a map Lipschitz on a set containing the image, composed
  -- with an AC function mapping into that set, is AC.
  -- ===================================================================
  have lipOnComp_ac : ∀ {F : ℝ → ℝ} {l : ℝ → ℝ} {K : NNReal} {s : Set ℝ},
      LipschitzOnWith K l s → ∀ {a b : ℝ}, AbsolutelyContinuousOnInterval F a b →
      (∀ t ∈ Set.uIcc a b, F t ∈ s) →
      AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
    intro F l K s hl a b hF hmaps
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    have hmem : ∀ i ∈ Finset.range E.1,
        (E.2 i).1 ∈ Set.uIcc a b ∧ (E.2 i).2 ∈ Set.uIcc a b := fun i hi => hE.1 i hi
    calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hl.dist_le_mul _ (hmaps _ (hmem i hi).1) _ (hmaps _ (hmem i hi).2)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- ===================================================================
  -- Helper 3: the round annulus is open.
  -- ===================================================================
  have isOpen_ann : ∀ (w : ℂ) (a b : ℝ), IsOpen (RoundAnnulus w a b) := by
    intro w a b
    have h1 : IsOpen {z : ℂ | a < dist z w} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    have h2 : IsOpen {z : ℂ | dist z w < b} :=
      isOpen_lt (continuous_id.dist continuous_const) continuous_const
    exact h1.inter h2
  -- ===================================================================
  -- Step 0: reduce to the centre `0`.
  -- ===================================================================
  have hreduce : ringModulus z₀ r R = ringModulus 0 r R := by
    unfold ringModulus
    set φ : ℂ → ℂ := fun z => z + z₀ with hφ
    have hhom : IsHomeomorph φ := by
      have : IsHomeomorph (Homeomorph.addRight z₀) := Homeomorph.isHomeomorph _
      simpa [hφ, Homeomorph.addRight] using this
    have hdiff : DifferentiableOn ℂ φ Set.univ :=
      (differentiable_id.add_const z₀).differentiableOn
    have key := curveModulus_conformal_invariant hhom hdiff
      (connectingCurveFamily (innerCircle 0 r) (outerCircle 0 R) (RoundAnnulus 0 r R))
    rw [← key]
    congr 1
    have hLipφ : LipschitzWith 1 φ :=
      LipschitzWith.of_dist_le_mul (fun x y => by simp [hφ, dist_eq_norm])
    have hLipχ : LipschitzWith 1 (fun z : ℂ => z - z₀) :=
      LipschitzWith.of_dist_le_mul (fun x y => by simp [dist_eq_norm])
    have hdistφ : ∀ (z : ℂ), dist (φ z) z₀ = dist z 0 := by
      intro z; simp [hφ, dist_eq_norm]
    have hdistχ : ∀ (z : ℂ), dist (z - z₀) 0 = dist z z₀ := by
      intro z; simp [dist_eq_norm]
    ext γ
    constructor
    · rintro ⟨hcont, hac, h0, h1, hsub⟩
      refine ⟨fun s => γ s - z₀, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · exact hcont.sub continuous_const
      · exact lipComp_ac hLipχ hac
      · simp only [innerCircle, Set.mem_ofPred_eq, hdistχ]
        simpa [innerCircle] using h0
      · simp only [outerCircle, Set.mem_ofPred_eq, hdistχ]
        simpa [outerCircle] using h1
      · intro t ht
        simp only [RoundAnnulus, Set.mem_ofPred_eq, hdistχ]
        simpa [RoundAnnulus] using hsub t ht
      · funext s; simp [hφ]
    · rintro ⟨γ₀, ⟨hcont, hac, h0, h1, hsub⟩, rfl⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have : Continuous (fun s => φ (γ₀ s)) := hLipφ.continuous.comp hcont
        simpa [hφ, Function.comp_def] using this
      · have : AbsolutelyContinuousOnInterval (fun s => φ (γ₀ s)) 0 1 := lipComp_ac hLipφ hac
        simpa [hφ, Function.comp_def] using this
      · simp only [Function.comp_apply, hφ, innerCircle, Set.mem_ofPred_eq]
        rw [show γ₀ 0 + z₀ = φ (γ₀ 0) from rfl, hdistφ]
        simpa [innerCircle] using h0
      · simp only [Function.comp_apply, hφ, outerCircle, Set.mem_ofPred_eq]
        rw [show γ₀ 1 + z₀ = φ (γ₀ 1) from rfl, hdistφ]
        simpa [outerCircle] using h1
      · intro t ht
        simp only [Function.comp_apply, hφ, RoundAnnulus, Set.mem_ofPred_eq]
        rw [show γ₀ t + z₀ = φ (γ₀ t) from rfl, hdistφ]
        simpa [RoundAnnulus] using hsub t ht
  rw [hreduce]
  -- ===================================================================
  -- The extremal radial density (centred at 0).
  -- ===================================================================
  set rho0 : ℂ → ℝ≥0∞ := fun z =>
    Set.indicator (RoundAnnulus 0 r R) (fun z => ENNReal.ofReal (1 / (‖z‖ * L))) z with hrho0
  have measurable_rho0 : Measurable rho0 := by
    apply Measurable.indicator _ (isOpen_ann 0 r R).measurableSet
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.div (measurable_norm.mul measurable_const))
  -- ===================================================================
  -- Energy: ∫⁻ rho0² = ofReal (2π/L).
  -- ===================================================================
  have rho0_energy : ∫⁻ z, (rho0 z) ^ 2 = ENNReal.ofReal (2 * Real.pi / L) := by
    rw [← Complex.lintegral_comp_polarCoord_symm (fun z => (rho0 z) ^ 2)]
    have hval : Set.EqOn
        (fun p : ℝ × ℝ => ENNReal.ofReal p.1 • (rho0 (Complex.polarCoord.symm p)) ^ 2)
        (fun p : ℝ × ℝ =>
          Set.indicator (Set.Ioo r R) (fun s => ENNReal.ofReal (1 / (s * L ^ 2))) p.1)
        Complex.polarCoord.target := by
      intro p hp
      simp only [Complex.polarCoord_target, Set.mem_prod, Set.mem_Ioi] at hp
      have hp1 : 0 < p.1 := hp.1
      have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
      simp only [hrho0, smul_eq_mul]
      by_cases hmem : Complex.polarCoord.symm p ∈ RoundAnnulus 0 r R
      · have hmemIoo : p.1 ∈ Set.Ioo r R := by
          simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_zero_right, hnorm] at hmem
          exact ⟨hmem.1, hmem.2⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmemIoo, hnorm]
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (le_of_lt hp1)]
        congr 1
        rw [div_pow, one_pow, mul_pow]
        rw [hL] at *
        field_simp
      · have hmemIoo : p.1 ∉ Set.Ioo r R := by
          simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_zero_right, hnorm] at hmem
          simpa only [Set.mem_Ioo] using hmem
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmemIoo]
        simp
    refine Eq.trans (setLIntegral_congr_fun (μ := volume)
      Complex.polarCoord.open_target.measurableSet hval) ?_
    change ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
        Set.indicator (Set.Ioo r R) (fun s => ENNReal.ofReal (1 / (s * L ^ 2))) p.1
          = ENNReal.ofReal (2 * π / L)
    rw [Measure.volume_eq_prod]
    rw [setLIntegral_prod]
    · have hinner : ∀ x : ℝ,
          ∫⁻ _y in Set.Ioo (-π) π,
            Set.indicator (Set.Ioo r R) (fun s => ENNReal.ofReal (1 / (s * L ^ 2))) x
            = Set.indicator (Set.Ioo r R) (fun s => ENNReal.ofReal (1 / (s * L ^ 2))) x
              * ENNReal.ofReal (2 * π) := by
        intro x
        rw [setLIntegral_const, Real.volume_Ioo]
        congr 2
        ring
      simp only [hinner]
      rw [lintegral_mul_const]
      · rw [setLIntegral_indicator measurableSet_Ioo]
        have hsetEq : Set.Ioo r R ∩ Set.Ioi (0 : ℝ) = Set.Ioo r R := by
          rw [Set.inter_eq_left]
          intro x hx; exact lt_trans hr hx.1
        rw [hsetEq]
        have hradial : ∫⁻ x in Set.Ioo r R, ENNReal.ofReal (1 / (x * L ^ 2))
            = ENNReal.ofReal (1 / L) := by
          rw [← ofReal_integral_eq_lintegral_ofReal]
          · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hrR.le]
            have : ∀ x : ℝ, 1 / (x * L ^ 2) = (1 / L ^ 2) * x⁻¹ := by
              intro x; rw [one_div, mul_inv, one_div]; ring
            simp_rw [this]
            rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hr (by linarith)]
            rw [← hL]
            congr 1
            rw [sq]
            field_simp
          · rw [← IntegrableOn]
            have hcontOn : ContinuousOn (fun x : ℝ => 1 / (x * L ^ 2)) (Set.Icc r R) := by
              apply ContinuousOn.div continuousOn_const
              · exact (continuous_id.mul continuous_const).continuousOn
              · intro x hx
                rw [Set.mem_Icc] at hx
                have : 0 < x := lt_of_lt_of_le hr hx.1
                positivity
            exact (hcontOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
          · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => ?_)
            have : 0 < x := lt_trans hr hx.1
            positivity
        rw [hradial, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hL]; ring
      · apply Measurable.indicator _ measurableSet_Ioo
        apply ENNReal.measurable_ofReal.comp
        exact (measurable_const.div ((measurable_id.mul measurable_const)))
    · apply Measurable.aemeasurable
      have hh : Measurable (fun s : ℝ => ENNReal.ofReal (1 / (s * L ^ 2))) :=
        ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.mul measurable_const))
      exact (hh.indicator measurableSet_Ioo).comp measurable_fst
  -- ===================================================================
  -- Helper 4: |deriv (‖γ ·‖) t| ≤ ‖deriv γ t‖.
  -- ===================================================================
  have norm_deriv_norm_le : ∀ {γ : ℝ → ℂ} {t : ℝ},
      HasDerivAt γ (deriv γ t) t →
      HasDerivAt (fun s => ‖γ s‖) (deriv (fun s => ‖γ s‖) t) t →
      |deriv (fun s => ‖γ s‖) t| ≤ ‖deriv γ t‖ := by
    intro γ t hγ hu
    rw [← Real.norm_eq_abs]
    have htu := hu.tendsto_slope
    have htγ := hγ.tendsto_slope
    have htu' : Filter.Tendsto (fun s => ‖slope (fun s => ‖γ s‖) t s‖) (𝓝[≠] t)
        (𝓝 ‖deriv (fun s => ‖γ s‖) t‖) := (continuous_norm.tendsto _).comp htu
    have htγ' : Filter.Tendsto (fun s => ‖slope γ t s‖) (𝓝[≠] t) (𝓝 ‖deriv γ t‖) :=
      (continuous_norm.tendsto _).comp htγ
    refine le_of_tendsto_of_tendsto htu' htγ' ?_
    filter_upwards with s
    rw [slope_def_module, slope_def_module, norm_smul, norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa using abs_norm_sub_norm_le (γ s) (γ t)
  -- ===================================================================
  -- Admissibility of rho0.
  -- ===================================================================
  have rho0_admissible : ∀ {γ : ℝ → ℂ}, AbsolutelyContinuousOnInterval γ 0 1 →
      γ 0 ∈ innerCircle 0 r → γ 1 ∈ outerCircle 0 R →
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, γ t ∈ RoundAnnulus 0 r R) →
      1 ≤ arcLengthLineIntegral rho0 γ := by
    intro γ hac h0 h1 hsub
    set u : ℝ → ℝ := fun t => ‖γ t‖ with hu
    have hu0 : u 0 = r := by
      simp only [hu, innerCircle, Set.mem_ofPred_eq, dist_zero_right] at h0 ⊢; exact h0
    have hu1 : u 1 = R := by
      simp only [hu, outerCircle, Set.mem_ofPred_eq, dist_zero_right] at h1 ⊢; exact h1
    have hubound : ∀ t ∈ Set.Icc (0 : ℝ) 1, r ≤ u t ∧ u t ≤ R := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h0t | h0t
      · subst h0t; rw [hu0]; exact ⟨le_refl _, hrR.le⟩
      rcases eq_or_lt_of_le ht.2 with h1t | h1t
      · rw [show t = 1 from h1t, hu1]; exact ⟨hrR.le, le_refl _⟩
      · have := hsub t ⟨h0t, h1t⟩
        simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_zero_right] at this
        exact ⟨this.1.le, this.2.le⟩
    have huAC : AbsolutelyContinuousOnInterval u 0 1 := lipComp_ac lipschitzWith_one_norm hac
    have humaps : ∀ t ∈ Set.uIcc (0 : ℝ) 1, u t ∈ Set.Icc r R := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact ⟨(hubound t ht).1, (hubound t ht).2⟩
    have hlogLip : LipschitzOnWith (NNReal.mk (1/r) (by positivity)) Real.log (Set.Icc r R) := by
      apply (convex_Icc r R).lipschitzOnWith_of_nnnorm_deriv_le
      · intro x hx
        rw [Set.mem_Icc] at hx
        exact Real.differentiableAt_log (lt_of_lt_of_le hr hx.1).ne'
      · intro x hx
        rw [Set.mem_Icc] at hx
        have hx0 : 0 < x := lt_of_lt_of_le hr hx.1
        rw [Real.deriv_log]
        rw [← NNReal.coe_le_coe]
        simp only [coe_nnnorm, Real.norm_eq_abs]
        change |x⁻¹| ≤ 1 / r
        rw [abs_of_pos (by positivity), one_div]
        exact inv_anti₀ hr hx.1
    set v : ℝ → ℝ := fun t => Real.log (u t) with hv
    have hvAC : AbsolutelyContinuousOnInterval v 0 1 := lipOnComp_ac hlogLip huAC humaps
    have hv0 : v 0 = Real.log r := by rw [hv]; simp [hu0]
    have hv1 : v 1 = Real.log R := by rw [hv]; simp [hu1]
    have hγdiff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → DifferentiableAt ℝ γ t :=
      hac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
    have hudiff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → DifferentiableAt ℝ u t :=
      huAC.ae_differentiableAt
    have hIccIoo : (volume.restrict (Set.Icc (0 : ℝ) 1)) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
      Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm
    have hline : arcLengthLineIntegral rho0 γ
        = ∫⁻ t in Set.Ioo (0 : ℝ) 1, rho0 (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      unfold arcLengthLineIntegral
      rw [hIccIoo]
    rw [hline]
    have hFTC : ∫ t in (0 : ℝ)..1, deriv v t = L := by
      rw [hvAC.integral_deriv_eq_sub, hv1, hv0, hL,
        Real.log_div (ne_of_gt (lt_trans hr hrR)) hr.ne']
    have hvint : IntervalIntegrable (deriv v) volume 0 1 := hvAC.intervalIntegrable_deriv
    have hvintOoc : IntegrableOn (deriv v) (Set.Ioo (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hvint
    have hvabsintOoc : IntegrableOn (fun t => |deriv v t|) (Set.Ioo (0 : ℝ) 1) volume :=
      hvintOoc.abs
    have hpoint : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        ENNReal.ofReal (1 / L) * ENNReal.ofReal |deriv v t|
          ≤ rho0 (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hγdiff, hudiff] with t htγ htu
      intro htmem
      have htuIcc : t ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le zero_le_one]; exact Set.Ioo_subset_Icc_self htmem
      have hγD : DifferentiableAt ℝ γ t := htγ htuIcc
      have huD : DifferentiableAt ℝ u t := htu htuIcc
      have hann : γ t ∈ RoundAnnulus 0 r R := hsub t htmem
      have hut_pos : 0 < u t := by
        simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_zero_right] at hann
        exact lt_trans hr hann.1
      have hrhoval : rho0 (γ t) = ENNReal.ofReal (1 / (u t * L)) := by
        simp only [hrho0, Set.indicator_of_mem hann, hu]
      have hdu_le : |deriv u t| ≤ ‖deriv γ t‖ :=
        norm_deriv_norm_le hγD.hasDerivAt huD.hasDerivAt
      have hvderiv : deriv v t = deriv u t / u t := by
        have : HasDerivAt v (deriv u t / u t) t := by
          have := huD.hasDerivAt.log (by rw [hu] at hut_pos ⊢; exact hut_pos.ne')
          simpa [hv, hu] using this
        exact this.deriv
      rw [hrhoval, hvderiv]
      have key1 : ENNReal.ofReal (1 / L) * ENNReal.ofReal |deriv u t / u t|
          = ENNReal.ofReal (1 / (u t * L)) * ENNReal.ofReal |deriv u t| := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [abs_div, abs_of_pos hut_pos]
        field_simp
      rw [key1]
      gcongr
      rw [show (‖deriv γ t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv γ t‖ from by
        rw [ofReal_norm, enorm_eq_nnnorm]]
      exact ENNReal.ofReal_le_ofReal hdu_le
    calc (1 : ℝ≥0∞)
        = ENNReal.ofReal (1 / L) * ENNReal.ofReal L := by
          rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hLpos.ne',
            ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (1 / L) * ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv v t| := by
          gcongr ?_ * ?_
          · exact le_rfl
          rw [← hFTC]
          calc ENNReal.ofReal (∫ t in (0 : ℝ)..1, deriv v t)
              ≤ ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, |deriv v t|) := by
                apply ENNReal.ofReal_le_ofReal
                rw [intervalIntegral.integral_of_le zero_le_one,
                  integral_Ioc_eq_integral_Ioo]
                apply setIntegral_mono_on hvintOoc hvabsintOoc measurableSet_Ioo
                intro x _; exact le_abs_self _
            _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv v t| := by
                rw [ofReal_integral_eq_lintegral_ofReal hvabsintOoc
                  (ae_restrict_of_forall_mem measurableSet_Ioo (fun x _ => abs_nonneg _))]
      _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / L) * ENNReal.ofReal |deriv v t| := by
          rw [lintegral_const_mul]
          exact ENNReal.measurable_ofReal.comp (_root_.continuous_abs.measurable.comp
            (measurable_deriv v))
      _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, rho0 (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) :=
          lintegral_mono_ae hpoint
  -- ===================================================================
  -- Upper bound.
  -- ===================================================================
  have hupper : ringModulus 0 r R ≤ ENNReal.ofReal (2 * Real.pi / L) := by
    unfold ringModulus curveModulus
    refine le_trans (iInf₂_le rho0 ?_) ?_
    · refine ⟨measurable_rho0, ?_⟩
      rintro γ ⟨_, hac, h0, h1, hsub⟩
      exact rho0_admissible hac h0 h1 hsub
    · exact le_of_eq rho0_energy
  -- ===================================================================
  -- The radial ray (centred at 0).
  -- ===================================================================
  set rayPoint : ℝ → ℝ → ℂ := fun θ s => s * (Real.cos θ + Real.sin θ * Complex.I) with hrayP
  have rayPoint_eq_symm : ∀ θ s : ℝ, rayPoint θ s = Complex.polarCoord.symm (s, θ) := by
    intro θ s
    rw [hrayP, Complex.polarCoord_symm_apply]
  set ray : ℝ → ℝ → ℝ → ℝ → ℂ := fun r' R' θ t => rayPoint θ (r' + t * (R' - r')) with hray
  -- ===================================================================
  -- Ray lower bound: ∫_r^R ρ(rayPoint θ s) ds ≥ 1 for admissible ρ.
  -- ===================================================================
  have ray_lower_bound : ∀ {ρ : ℂ → ℝ≥0∞}, IsAdmissibleDensity ρ
      (connectingCurveFamily (innerCircle 0 r) (outerCircle 0 R) (RoundAnnulus 0 r R)) →
      ∀ {θ : ℝ}, 1 ≤ ∫⁻ s in Set.Ioo r R, ρ (rayPoint θ s) := by
    intro ρ hρ θ
    set e : ℂ := (Real.cos θ + Real.sin θ * Complex.I) with he
    have hnorme : ‖e‖ = 1 := by
      have : e = Complex.exp (θ * Complex.I) := by
        rw [he, Complex.exp_mul_I]; push_cast; ring
      rw [this, Complex.norm_exp]
      simp
    set γ : ℝ → ℂ := ray r R θ with hγ
    have hγeq : ∀ t, γ t = (r + t * (R - r) : ℝ) * e := by
      intro t; simp only [hγ, hray, hrayP, he]
    have hderiv : ∀ t, HasDerivAt γ (((R - r : ℝ) : ℂ) * e) t := by
      intro t
      have hr1 : HasDerivAt (fun t : ℝ => (r + t * (R - r) : ℝ)) (R - r) t := by
        simpa using ((hasDerivAt_id t).mul_const (R - r)).const_add r
      have h1 : HasDerivAt (fun t : ℝ => ((r + t * (R - r) : ℝ) : ℂ)) ((R - r : ℝ) : ℂ) t :=
        hr1.ofReal_comp
      have h2 := h1.mul_const e
      apply h2.congr_of_eventuallyEq
      filter_upwards with s using (hγeq s).symm
    have hderiveq : ∀ t, deriv γ t = ((R - r : ℝ) : ℂ) * e := fun t => (hderiv t).deriv
    have hnormderiv : ∀ t, ‖deriv γ t‖ = R - r := by
      intro t
      rw [hderiveq, norm_mul, hnorme, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    have hnormγ : ∀ t, ‖γ t‖ = |r + t * (R - r)| := by
      intro t; rw [hγeq, norm_mul, hnorme, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hcontγ : Continuous γ := by
      have hreal : Continuous (fun t : ℝ => (r + t * (R - r) : ℝ)) :=
        continuous_const.add (continuous_id.mul continuous_const)
      have : Continuous (fun t : ℝ => (r + t * (R - r) : ℝ) * e) :=
        (Complex.continuous_ofReal.comp hreal).mul continuous_const
      exact this.congr (fun t => (hγeq t).symm)
    have hlipγ : LipschitzWith (NNReal.mk (R - r) (by linarith)) γ := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, dist_eq_norm, hγeq, hγeq, ← sub_mul, norm_mul, hnorme, mul_one]
      rw [show ((r + x * (R - r) : ℝ) : ℂ) - ((r + y * (R - r) : ℝ) : ℂ)
          = (((x - y) * (R - r) : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (show (0:ℝ) < R - r by linarith)]
      change |x - y| * (R - r) ≤ (R - r) * ‖x - y‖
      rw [Real.norm_eq_abs]
      rw [mul_comm]
    have hacγ : AbsolutelyContinuousOnInterval γ 0 1 :=
      (hlipγ.lipschitzOnWith (s := Set.uIcc 0 1)).absolutelyContinuousOnInterval
    have hmemf : γ ∈ connectingCurveFamily (innerCircle 0 r) (outerCircle 0 R)
        (RoundAnnulus 0 r R) := by
      refine ⟨hcontγ, hacγ, ?_, ?_, ?_⟩
      · simp only [innerCircle, Set.mem_ofPred_eq, dist_zero_right, hnormγ]
        rw [show r + (0:ℝ) * (R - r) = r by ring, abs_of_pos hr]
      · simp only [outerCircle, Set.mem_ofPred_eq, dist_zero_right, hnormγ]
        rw [show r + (1:ℝ) * (R - r) = R by ring, abs_of_pos (by linarith)]
      · intro t ht
        simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_zero_right, hnormγ]
        have hpos : 0 < r + t * (R - r) := by nlinarith [ht.1, ht.2, hrR]
        rw [abs_of_pos hpos]
        exact ⟨by nlinarith [ht.1, hrR], by nlinarith [ht.2, hrR]⟩
    have hadm : 1 ≤ arcLengthLineIntegral ρ γ := hρ.2 γ hmemf
    have hcontrp : Continuous (fun s : ℝ => rayPoint θ s) :=
      Complex.continuous_ofReal.mul continuous_const
    have hmeast : Measurable (fun t : ℝ => ρ (rayPoint θ (r + t * (R - r)))) :=
      hρ.1.comp (hcontrp.comp
        (continuous_const.add (continuous_id.mul continuous_const))).measurable
    have himg : (fun t : ℝ => r + t * (R - r)) '' Set.Ioo 0 1 = Set.Ioo r R := by
      ext s
      simp only [Set.mem_image, Set.mem_Ioo]
      constructor
      · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
        exact ⟨by nlinarith, by nlinarith⟩
      · intro ⟨hsr, hsR⟩
        refine ⟨(s - r) / (R - r), ⟨by apply div_pos <;> linarith, ?_⟩, ?_⟩
        · rw [div_lt_one (by linarith)]; linarith
        · rw [div_mul_cancel₀ _ (show (R - r) ≠ 0 by linarith)]; ring
    have hcov : ∫⁻ s in Set.Ioo r R, ρ (rayPoint θ s)
        = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (R - r) * ρ (rayPoint θ (r + t * (R - r))) := by
      rw [← himg]
      rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
        (f := fun t => r + t * (R - r)) (f' := fun _ => R - r) ?_ ?_]
      · apply lintegral_congr
        intro t
        rw [abs_of_pos (show (0:ℝ) < R - r by linarith)]
      · intro x _
        have : HasDerivAt (fun t : ℝ => r + t * (R - r)) (R - r) x := by
          simpa using ((hasDerivAt_id x).mul_const (R - r)).const_add r
        exact this.hasDerivWithinAt
      · intro a _ b _ hab
        simp only at hab
        have hRr : (R - r) ≠ 0 := by linarith
        have : a * (R - r) = b * (R - r) := by linarith
        exact mul_right_cancel₀ hRr this
    have harc : arcLengthLineIntegral ρ γ
        = ∫⁻ s in Set.Ioo r R, ρ (rayPoint θ s) := by
      rw [hcov]
      unfold arcLengthLineIntegral
      rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm]
      apply lintegral_congr
      intro t
      rw [show (‖deriv γ t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv γ t‖ from by
        rw [ofReal_norm, enorm_eq_nnnorm], hnormderiv, mul_comm]
    rw [← harc]
    exact hadm
  -- ===================================================================
  -- ∫_r^R 1/s ds = log(R/r) = L.
  -- ===================================================================
  have lintegral_inv_radial : ∫⁻ s in Set.Ioo r R, ENNReal.ofReal s⁻¹ = ENNReal.ofReal L := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [hL]
      congr 1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hrR.le]
      rw [integral_inv_of_pos hr (lt_trans hr hrR)]
    · have hcontOn : ContinuousOn (fun s : ℝ => s⁻¹) (Set.Icc r R) := by
        apply ContinuousOn.inv₀ continuousOn_id
        intro x hx; rw [Set.mem_Icc] at hx; exact (lt_of_lt_of_le hr hx.1).ne'
      exact (hcontOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
    · exact ae_restrict_of_forall_mem measurableSet_Ioo
        (fun s hs => inv_nonneg.mpr (by linarith [hs.1]))
  -- ===================================================================
  -- Cauchy–Schwarz on each ray: ∫_r^R ρ² s ds ≥ 1/L.
  -- ===================================================================
  have radial_energy_lower : ∀ {ρ : ℂ → ℝ≥0∞}, IsAdmissibleDensity ρ
      (connectingCurveFamily (innerCircle 0 r) (outerCircle 0 R) (RoundAnnulus 0 r R)) →
      ∀ {θ : ℝ}, ENNReal.ofReal (1 / L)
        ≤ ∫⁻ s in Set.Ioo r R, (ρ (rayPoint θ s)) ^ 2 * ENNReal.ofReal s := by
    intro ρ hρ θ
    set μ := volume.restrict (Set.Ioo r R) with hμ
    set A : ℝ≥0∞ := ∫⁻ s in Set.Ioo r R, (ρ (rayPoint θ s)) ^ 2 * ENNReal.ofReal s with hA
    set B : ℝ≥0∞ := ∫⁻ s in Set.Ioo r R, ENNReal.ofReal s⁻¹ with hB
    have hBeq : B = ENNReal.ofReal L := lintegral_inv_radial
    set f : ℝ → ℝ≥0∞ := fun s => ρ (rayPoint θ s) * ENNReal.ofReal (Real.sqrt s) with hf
    set g : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.sqrt s)⁻¹ with hg
    have hcontrp : Continuous (fun s : ℝ => rayPoint θ s) :=
      Complex.continuous_ofReal.mul continuous_const
    have hmeasf : AEMeasurable f μ := by
      apply Measurable.aemeasurable
      apply Measurable.mul
      · exact hρ.1.comp hcontrp.measurable
      · exact ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable)
    have hmeasg : AEMeasurable g μ :=
      (ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.inv)).aemeasurable
    have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
      (Real.HolderConjugate.two_two) hmeasf hmeasg
    have hone : 1 ≤ ∫⁻ s, (f * g) s ∂μ := by
      have hfgeq : ∫⁻ s, (f * g) s ∂μ = ∫⁻ s in Set.Ioo r R, ρ (rayPoint θ s) := by
        rw [hμ]
        apply lintegral_congr_ae
        refine ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => ?_)
        have hs0 : 0 < s := lt_trans hr hs.1
        have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
        simp only [Pi.mul_apply, hf, hg]
        rw [mul_assoc, ← ENNReal.ofReal_mul hsqrt.le, mul_inv_cancel₀ hsqrt.ne',
          ENNReal.ofReal_one, mul_one]
      rw [hfgeq]
      exact ray_lower_bound hρ
    have hfsq : ∫⁻ s, f s ^ (2:ℝ) ∂μ = A := by
      rw [hA, hμ]
      apply lintegral_congr_ae
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => ?_)
      have hs0 : 0 < s := lt_trans hr hs.1
      simp only [hf]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_two, ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg s), Real.sq_sqrt hs0.le]
    have hgsq : ∫⁻ s, g s ^ (2:ℝ) ∂μ = B := by
      rw [hB, hμ]
      apply lintegral_congr_ae
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => ?_)
      have hs0 : 0 < s := lt_trans hr hs.1
      have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
      simp only [hg]
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity), inv_pow, Real.sq_sqrt hs0.le]
    rw [hfsq, hgsq] at hholder
    rw [show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num] at hholder
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)] at hholder
    have hAB : (1:ℝ≥0∞) ≤ A * B := by
      have h := ENNReal.rpow_le_rpow (le_trans hone hholder) (show (0:ℝ) ≤ 2 by norm_num)
      rwa [ENNReal.one_rpow, ← ENNReal.rpow_mul,
        show (2:ℝ)⁻¹ * (2:ℝ) = 1 by norm_num, ENNReal.rpow_one] at h
    rw [show ENNReal.ofReal (1 / L) = (ENNReal.ofReal L)⁻¹ from by
      rw [← ENNReal.ofReal_inv_of_pos hLpos, one_div]]
    rw [← hBeq]
    have hBne0 : B ≠ 0 := by rw [hBeq, Ne, ENNReal.ofReal_eq_zero, not_le]; exact hLpos
    have hBnetop : B ≠ ∞ := by rw [hBeq]; exact ENNReal.ofReal_ne_top
    rw [ENNReal.inv_le_iff_le_mul (fun _ => hBne0) (fun h => absurd h hBnetop)]
    rwa [mul_comm]
  -- ===================================================================
  -- Lower bound.
  -- ===================================================================
  have hlower : ENNReal.ofReal (2 * Real.pi / L) ≤ ringModulus 0 r R := by
    unfold ringModulus curveModulus
    refine le_iInf₂ ?_
    rintro ρ ⟨hρmeas, hρadm⟩
    have hρ : IsAdmissibleDensity ρ
        (connectingCurveFamily (innerCircle 0 r) (outerCircle 0 R) (RoundAnnulus 0 r R)) :=
      ⟨hρmeas, hρadm⟩
    rw [← Complex.lintegral_comp_polarCoord_symm (fun z => (ρ z) ^ 2)]
    have hval : ∀ p ∈ Complex.polarCoord.target,
        ENNReal.ofReal p.1 • (ρ (Complex.polarCoord.symm p)) ^ 2
          = (ρ (rayPoint p.2 p.1)) ^ 2 * ENNReal.ofReal p.1 := by
      intro p _
      rw [smul_eq_mul, mul_comm]
      congr 2
      rw [rayPoint_eq_symm]
    have hrwInt : ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • (ρ (Complex.polarCoord.symm p)) ^ 2
        = ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
            (ρ (rayPoint p.2 p.1)) ^ 2 * ENNReal.ofReal p.1 :=
      setLIntegral_congr_fun (μ := volume) Complex.polarCoord.open_target.measurableSet
        (fun p hp => hval p hp)
    refine le_of_le_of_eq ?_ hrwInt.symm
    rw [Measure.volume_eq_prod, setLIntegral_prod_symm _ ?_]
    · calc ENNReal.ofReal (2 * Real.pi / L)
          = ∫⁻ _θ in Set.Ioo (-π) π, ENNReal.ofReal (1 / L) := by
            rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [show -π = -(π:ℝ) from rfl]
            field_simp
            ring
        _ ≤ ∫⁻ θ in Set.Ioo (-π) π,
              ∫⁻ s in Set.Ioi (0 : ℝ), (ρ (rayPoint θ s)) ^ 2 * ENNReal.ofReal s := by
            apply lintegral_mono_ae
            refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ _ => ?_)
            calc ENNReal.ofReal (1 / L)
                ≤ ∫⁻ s in Set.Ioo r R, (ρ (rayPoint θ s)) ^ 2 * ENNReal.ofReal s :=
                  radial_energy_lower hρ
              _ ≤ ∫⁻ s in Set.Ioi (0 : ℝ), (ρ (rayPoint θ s)) ^ 2 * ENNReal.ofReal s := by
                  apply lintegral_mono_set
                  intro s hs; exact lt_trans hr hs.1
    · apply Measurable.aemeasurable
      have hcontray : Continuous (fun p : ℝ × ℝ => rayPoint p.2 p.1) := by
        simp only [hrayP]
        exact (Complex.continuous_ofReal.comp continuous_fst).mul
          ((Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_snd)).add
            ((Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_snd)).mul
              continuous_const))
      apply Measurable.mul
      · exact (hρmeas.comp hcontray.measurable).pow_const 2
      · exact ENNReal.measurable_ofReal.comp measurable_fst
  rw [hL] at hupper hlower
  exact le_antisymm hupper hlower

/-- The **radial extremal density** of the round annulus `RoundAnnulus z₀ r R`:
`ρ(z) = 1 / (‖z - z₀‖ · log (R / r))`, supported on the annulus. This is the density realizing the
round-annulus modulus `ringModulus_roundAnnulus`. -/
noncomputable def radialDensity (z₀ : ℂ) (r R : ℝ) : ℂ → ℝ≥0∞ :=
  Set.indicator (RoundAnnulus z₀ r R)
    (fun z => ENNReal.ofReal (1 / (‖z - z₀‖ * Real.log (R / r))))

/-- **The radial extremal density is admissible for the round-annulus connecting family.** Every
absolutely continuous curve joining the inner circle `innerCircle z₀ r` to the outer circle
`outerCircle z₀ R` inside `RoundAnnulus z₀ r R` sweeps the full radial range `[r, R]`, so along it
`∫ 1/(‖z - z₀‖ · log (R/r)) ‖dz‖ ≥ (1/log (R/r)) |log R - log r| = 1`. -/
theorem isAdmissibleDensity_radialDensity_roundAnnulus {z₀ : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    IsAdmissibleDensity (radialDensity z₀ r R)
      (connectingCurveFamily (innerCircle z₀ r) (outerCircle z₀ R) (RoundAnnulus z₀ r R)) := by
  set L := Real.log (R / r) with hL
  have hRr1 : 1 < R / r := (one_lt_div hr).mpr hrR
  have hLpos : 0 < L := Real.log_pos hRr1
  -- Helper: a Lipschitz map composed with an AC function is AC.
  have lipComp_ac : ∀ {Y : Type} [PseudoMetricSpace Y] {F : ℝ → ℂ} {l : ℂ → Y} {K : NNReal},
      LipschitzWith K l → ∀ {a b : ℝ}, AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
    intro Y _ F l K hl a b hF
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
  -- Helper: a map Lipschitz on a set containing the image, composed with an AC function mapping
  -- into that set, is AC.
  have lipOnComp_ac : ∀ {F : ℝ → ℝ} {l : ℝ → ℝ} {K : NNReal} {s : Set ℝ},
      LipschitzOnWith K l s → ∀ {a b : ℝ}, AbsolutelyContinuousOnInterval F a b →
      (∀ t ∈ Set.uIcc a b, F t ∈ s) →
      AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
    intro F l K s hl a b hF hmaps
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    have hmem : ∀ i ∈ Finset.range E.1,
        (E.2 i).1 ∈ Set.uIcc a b ∧ (E.2 i).2 ∈ Set.uIcc a b := fun i hi => hE.1 i hi
    calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hl.dist_le_mul _ (hmaps _ (hmem i hi).1) _ (hmaps _ (hmem i hi).2)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- Helper: the round annulus is open.
  have isOpen_ann : ∀ (w : ℂ) (a b : ℝ), IsOpen (RoundAnnulus w a b) := by
    intro w a b
    have h1 : IsOpen {z : ℂ | a < dist z w} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    have h2 : IsOpen {z : ℂ | dist z w < b} :=
      isOpen_lt (continuous_id.dist continuous_const) continuous_const
    exact h1.inter h2
  -- The shifted-norm map `w ↦ ‖w - z₀‖` is 1-Lipschitz.
  have hLipShift : LipschitzWith 1 (fun w : ℂ => ‖w - z₀‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    calc |‖x - z₀‖ - ‖y - z₀‖| ≤ ‖(x - z₀) - (y - z₀)‖ := abs_norm_sub_norm_le _ _
      _ = dist x y := by rw [sub_sub_sub_cancel_right, dist_eq_norm]
  -- Helper: |deriv (‖γ · - z₀‖) t| ≤ ‖deriv γ t‖.
  have norm_deriv_norm_le : ∀ {γ : ℝ → ℂ} {t : ℝ},
      HasDerivAt γ (deriv γ t) t →
      HasDerivAt (fun s => ‖γ s - z₀‖) (deriv (fun s => ‖γ s - z₀‖) t) t →
      |deriv (fun s => ‖γ s - z₀‖) t| ≤ ‖deriv γ t‖ := by
    intro γ t hγ hu
    rw [← Real.norm_eq_abs]
    have htu := hu.tendsto_slope
    have htγ := hγ.tendsto_slope
    have htu' : Filter.Tendsto (fun s => ‖slope (fun s => ‖γ s - z₀‖) t s‖) (𝓝[≠] t)
        (𝓝 ‖deriv (fun s => ‖γ s - z₀‖) t‖) := (continuous_norm.tendsto _).comp htu
    have htγ' : Filter.Tendsto (fun s => ‖slope γ t s‖) (𝓝[≠] t) (𝓝 ‖deriv γ t‖) :=
      (continuous_norm.tendsto _).comp htγ
    refine le_of_tendsto_of_tendsto htu' htγ' ?_
    filter_upwards with s
    rw [slope_def_module, slope_def_module, norm_smul, norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have : ‖(γ s - z₀) - (γ t - z₀)‖ = ‖γ s - γ t‖ := by rw [sub_sub_sub_cancel_right]
    simpa [this] using abs_norm_sub_norm_le (γ s - z₀) (γ t - z₀)
  -- Measurability of the radial density.
  refine ⟨?_, ?_⟩
  · unfold radialDensity
    apply Measurable.indicator _ (isOpen_ann z₀ r R).measurableSet
    apply ENNReal.measurable_ofReal.comp
    apply measurable_const.div
    exact ((continuous_id.sub continuous_const).norm.measurable).mul measurable_const
  -- Admissibility.
  · rintro γ ⟨_, hac, h0, h1, hsub⟩
    set u : ℝ → ℝ := fun t => ‖γ t - z₀‖ with hu
    have hu0 : u 0 = r := by
      simp only [hu, innerCircle, Set.mem_ofPred_eq, dist_eq_norm] at h0 ⊢; exact h0
    have hu1 : u 1 = R := by
      simp only [hu, outerCircle, Set.mem_ofPred_eq, dist_eq_norm] at h1 ⊢; exact h1
    have hubound : ∀ t ∈ Set.Icc (0 : ℝ) 1, r ≤ u t ∧ u t ≤ R := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h0t | h0t
      · subst h0t; rw [hu0]; exact ⟨le_refl _, hrR.le⟩
      rcases eq_or_lt_of_le ht.2 with h1t | h1t
      · rw [show t = 1 from h1t, hu1]; exact ⟨hrR.le, le_refl _⟩
      · have := hsub t ⟨h0t, h1t⟩
        simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_eq_norm] at this
        exact ⟨this.1.le, this.2.le⟩
    have huAC : AbsolutelyContinuousOnInterval u 0 1 := lipComp_ac hLipShift hac
    have humaps : ∀ t ∈ Set.uIcc (0 : ℝ) 1, u t ∈ Set.Icc r R := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact ⟨(hubound t ht).1, (hubound t ht).2⟩
    have hlogLip : LipschitzOnWith (NNReal.mk (1/r) (by positivity)) Real.log (Set.Icc r R) := by
      apply (convex_Icc r R).lipschitzOnWith_of_nnnorm_deriv_le
      · intro x hx
        rw [Set.mem_Icc] at hx
        exact Real.differentiableAt_log (lt_of_lt_of_le hr hx.1).ne'
      · intro x hx
        rw [Set.mem_Icc] at hx
        have hx0 : 0 < x := lt_of_lt_of_le hr hx.1
        rw [Real.deriv_log]
        rw [← NNReal.coe_le_coe]
        simp only [coe_nnnorm, Real.norm_eq_abs]
        change |x⁻¹| ≤ 1 / r
        rw [abs_of_pos (by positivity), one_div]
        exact inv_anti₀ hr hx.1
    set v : ℝ → ℝ := fun t => Real.log (u t) with hv
    have hvAC : AbsolutelyContinuousOnInterval v 0 1 := lipOnComp_ac hlogLip huAC humaps
    have hv0 : v 0 = Real.log r := by rw [hv]; simp [hu0]
    have hv1 : v 1 = Real.log R := by rw [hv]; simp [hu1]
    have hγdiff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → DifferentiableAt ℝ γ t :=
      hac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
    have hudiff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → DifferentiableAt ℝ u t :=
      huAC.ae_differentiableAt
    have hIccIoo : (volume.restrict (Set.Icc (0 : ℝ) 1)) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
      Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm
    have hline : arcLengthLineIntegral (radialDensity z₀ r R) γ
        = ∫⁻ t in Set.Ioo (0 : ℝ) 1, radialDensity z₀ r R (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      unfold arcLengthLineIntegral
      rw [hIccIoo]
    rw [hline]
    have hFTC : ∫ t in (0 : ℝ)..1, deriv v t = L := by
      rw [hvAC.integral_deriv_eq_sub, hv1, hv0, hL,
        Real.log_div (ne_of_gt (lt_trans hr hrR)) hr.ne']
    have hvint : IntervalIntegrable (deriv v) volume 0 1 := hvAC.intervalIntegrable_deriv
    have hvintOoc : IntegrableOn (deriv v) (Set.Ioo (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hvint
    have hvabsintOoc : IntegrableOn (fun t => |deriv v t|) (Set.Ioo (0 : ℝ) 1) volume :=
      hvintOoc.abs
    have hpoint : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        ENNReal.ofReal (1 / L) * ENNReal.ofReal |deriv v t|
          ≤ radialDensity z₀ r R (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hγdiff, hudiff] with t htγ htu
      intro htmem
      have htuIcc : t ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le zero_le_one]; exact Set.Ioo_subset_Icc_self htmem
      have hγD : DifferentiableAt ℝ γ t := htγ htuIcc
      have huD : DifferentiableAt ℝ u t := htu htuIcc
      have hann : γ t ∈ RoundAnnulus z₀ r R := hsub t htmem
      have hut_pos : 0 < u t := by
        simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_eq_norm] at hann
        exact lt_trans hr hann.1
      have hrhoval : radialDensity z₀ r R (γ t) = ENNReal.ofReal (1 / (u t * L)) := by
        simp only [radialDensity, Set.indicator_of_mem hann, hu, hL]
      have hdu_le : |deriv u t| ≤ ‖deriv γ t‖ :=
        norm_deriv_norm_le hγD.hasDerivAt huD.hasDerivAt
      have hvderiv : deriv v t = deriv u t / u t := by
        have : HasDerivAt v (deriv u t / u t) t := by
          have := huD.hasDerivAt.log (by rw [hu] at hut_pos ⊢; exact hut_pos.ne')
          simpa [hv, hu] using this
        exact this.deriv
      rw [hrhoval, hvderiv]
      have key1 : ENNReal.ofReal (1 / L) * ENNReal.ofReal |deriv u t / u t|
          = ENNReal.ofReal (1 / (u t * L)) * ENNReal.ofReal |deriv u t| := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [abs_div, abs_of_pos hut_pos]
        field_simp
      rw [key1]
      gcongr
      rw [show (‖deriv γ t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv γ t‖ from by
        rw [ofReal_norm, enorm_eq_nnnorm]]
      exact ENNReal.ofReal_le_ofReal hdu_le
    calc (1 : ℝ≥0∞)
        = ENNReal.ofReal (1 / L) * ENNReal.ofReal L := by
          rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hLpos.ne',
            ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (1 / L) * ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv v t| := by
          gcongr ?_ * ?_
          · exact le_rfl
          rw [← hFTC]
          calc ENNReal.ofReal (∫ t in (0 : ℝ)..1, deriv v t)
              ≤ ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, |deriv v t|) := by
                apply ENNReal.ofReal_le_ofReal
                rw [intervalIntegral.integral_of_le zero_le_one,
                  integral_Ioc_eq_integral_Ioo]
                apply setIntegral_mono_on hvintOoc hvabsintOoc measurableSet_Ioo
                intro x _; exact le_abs_self _
            _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv v t| := by
                rw [ofReal_integral_eq_lintegral_ofReal hvabsintOoc
                  (ae_restrict_of_forall_mem measurableSet_Ioo (fun x _ => abs_nonneg _))]
      _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / L) * ENNReal.ofReal |deriv v t| := by
          rw [lintegral_const_mul]
          exact ENNReal.measurable_ofReal.comp (_root_.continuous_abs.measurable.comp
            (measurable_deriv v))
      _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, radialDensity z₀ r R (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) :=
          lintegral_mono_ae hpoint

/-- **The energy of the radial extremal density equals the round-annulus modulus.** The area energy
`∫∫ (radialDensity z₀ r R)²` of the radial density evaluates to `2π / log (R / r)`, which is the
value of `ringModulus z₀ r R`. This is the sharp energy achieving the round-annulus modulus. -/
theorem lintegral_radialDensity_sq {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∫⁻ z, (radialDensity z₀ r R z) ^ 2 = ringModulus z₀ r R := by
  set L := Real.log (R / r) with hL
  have hRr1 : 1 < R / r := (one_lt_div hr).mpr hrR
  have hLpos : 0 < L := Real.log_pos hRr1
  -- Translate the energy integral to the centre `0`.
  have hshift : ∀ z, radialDensity z₀ r R z = radialDensity 0 r R (z - z₀) := by
    intro z
    unfold radialDensity
    by_cases hz : z ∈ RoundAnnulus z₀ r R
    · have hz0 : z - z₀ ∈ RoundAnnulus 0 r R := by
        simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_zero_right] at *
        rw [show ‖z - z₀‖ = dist z z₀ from (dist_eq_norm z z₀).symm]; exact hz
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz0]
      simp [sub_zero]
    · have hz0 : z - z₀ ∉ RoundAnnulus 0 r R := by
        simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_zero_right] at *
        rw [show ‖z - z₀‖ = dist z z₀ from (dist_eq_norm z z₀).symm]; exact hz
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz0]
  have htrans : ∫⁻ z, (radialDensity z₀ r R z) ^ 2 = ∫⁻ z, (radialDensity 0 r R z) ^ 2 := by
    simp_rw [hshift]
    exact lintegral_sub_right_eq_self (fun z => (radialDensity 0 r R z) ^ 2) z₀
  rw [htrans, ringModulus_roundAnnulus hr hrR, ← hL]
  -- The centre-0 radial density coincides with the density of `ringModulus_roundAnnulus`.
  set rho0 : ℂ → ℝ≥0∞ := fun z =>
    Set.indicator (RoundAnnulus 0 r R) (fun z => ENNReal.ofReal (1 / (‖z‖ * L))) z with hrho0
  have hrho0eq : ∀ z, radialDensity 0 r R z = rho0 z := by
    intro z
    unfold radialDensity
    simp only [hrho0, sub_zero, hL]
  simp_rw [hrho0eq]
  -- Polar-coordinate computation of the energy, matching `ringModulus_roundAnnulus`.
  rw [← Complex.lintegral_comp_polarCoord_symm (fun z => (rho0 z) ^ 2)]
  have hval : Set.EqOn
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 • (rho0 (Complex.polarCoord.symm p)) ^ 2)
      (fun p : ℝ × ℝ =>
        Set.indicator (Set.Ioo r R) (fun s => ENNReal.ofReal (1 / (s * L ^ 2))) p.1)
      Complex.polarCoord.target := by
    intro p hp
    simp only [Complex.polarCoord_target, Set.mem_prod, Set.mem_Ioi] at hp
    have hp1 : 0 < p.1 := hp.1
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    simp only [hrho0, smul_eq_mul]
    by_cases hmem : Complex.polarCoord.symm p ∈ RoundAnnulus 0 r R
    · have hmemIoo : p.1 ∈ Set.Ioo r R := by
        simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_zero_right, hnorm] at hmem
        exact ⟨hmem.1, hmem.2⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmemIoo, hnorm]
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (le_of_lt hp1)]
      congr 1
      rw [div_pow, one_pow, mul_pow]
      field_simp
    · have hmemIoo : p.1 ∉ Set.Ioo r R := by
        simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_zero_right, hnorm] at hmem
        simpa only [Set.mem_Ioo] using hmem
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmemIoo]
      simp
  refine Eq.trans (setLIntegral_congr_fun (μ := volume)
    Complex.polarCoord.open_target.measurableSet hval) ?_
  change ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
      Set.indicator (Set.Ioo r R) (fun s => ENNReal.ofReal (1 / (s * L ^ 2))) p.1
        = ENNReal.ofReal (2 * π / L)
  rw [Measure.volume_eq_prod]
  rw [setLIntegral_prod]
  · have hinner : ∀ x : ℝ,
        ∫⁻ _y in Set.Ioo (-π) π,
          Set.indicator (Set.Ioo r R) (fun s => ENNReal.ofReal (1 / (s * L ^ 2))) x
          = Set.indicator (Set.Ioo r R) (fun s => ENNReal.ofReal (1 / (s * L ^ 2))) x
            * ENNReal.ofReal (2 * π) := by
      intro x
      rw [setLIntegral_const, Real.volume_Ioo]
      congr 2
      ring
    simp only [hinner]
    rw [lintegral_mul_const]
    · rw [setLIntegral_indicator measurableSet_Ioo]
      have hsetEq : Set.Ioo r R ∩ Set.Ioi (0 : ℝ) = Set.Ioo r R := by
        rw [Set.inter_eq_left]
        intro x hx; exact lt_trans hr hx.1
      rw [hsetEq]
      have hradial : ∫⁻ x in Set.Ioo r R, ENNReal.ofReal (1 / (x * L ^ 2))
          = ENNReal.ofReal (1 / L) := by
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hrR.le]
          have hrw : ∀ x : ℝ, 1 / (x * L ^ 2) = (1 / L ^ 2) * x⁻¹ := by
            intro x; rw [one_div, mul_inv, one_div]; ring
          simp_rw [hrw]
          rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hr (by linarith)]
          rw [← hL]
          congr 1
          rw [sq]
          field_simp
        · rw [← IntegrableOn]
          have hcontOn : ContinuousOn (fun x : ℝ => 1 / (x * L ^ 2)) (Set.Icc r R) := by
            apply ContinuousOn.div continuousOn_const
            · exact (continuous_id.mul continuous_const).continuousOn
            · intro x hx
              rw [Set.mem_Icc] at hx
              have : 0 < x := lt_of_lt_of_le hr hx.1
              positivity
          exact (hcontOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
        · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => ?_)
          have : 0 < x := lt_trans hr hx.1
          positivity
      rw [hradial, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hL]; ring
    · apply Measurable.indicator _ measurableSet_Ioo
      apply ENNReal.measurable_ofReal.comp
      exact (measurable_const.div ((measurable_id.mul measurable_const)))
  · apply Measurable.aemeasurable
    have hh : Measurable (fun s : ℝ => ENNReal.ofReal (1 / (s * L ^ 2))) :=
      ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.mul measurable_const))
    exact (hh.indicator measurableSet_Ioo).comp measurable_fst

/-- The **exponential quadrilateral realization of a round annulus**. For a centre `z₀` and radii
`0 < r < R` the closed unit square is mapped onto the slit round annulus
`{z₀ + w : r ≤ |w| ≤ R, 0 ≤ arg w ≤ π}` by
`(p₁, p₂) ↦ z₀ + exp((log r + p₁·(log R − log r)) + i·(π·p₂))`.
The radial coordinate `p₁` controls `|w| = exp(log r + p₁·(log R − log r)) ∈ [r, R]` and the angular
coordinate `p₂` controls `arg w = π·p₂ ∈ [0, π]`. Since the angular width `π` is strictly less than
`2π`, the map is injective on the closed square: taking norms recovers `p₁` from `|w|` (strict
monotonicity of the radial exponent), and the imaginary part recovers `p₂ ∈ [0, 1]` from the
argument within a single `2π`-window. Its left side lies on the inner circle `{|w| = r}`, its right
side on the outer circle `{|w| = R}`, and its image in the closed annulus. -/
noncomputable def Quadrilateral.ofRoundAnnulus (z₀ : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    Quadrilateral where
  toFun p := z₀ + Complex.exp (Complex.ofReal (Real.log r + p.1 * (Real.log R - Real.log r))
    + Complex.I * Complex.ofReal (Real.pi * p.2))
  continuous_toFun := by
    refine continuous_const.add (Complex.continuous_exp.comp ?_)
    refine Continuous.add ?_ ?_
    · exact Complex.continuous_ofReal.comp
        (continuous_const.add ((continuous_fst).mul continuous_const))
    · exact continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_snd))
  injOn_unitSquare := by
    intro p hp q hq hpq
    simp only [unitSquare, Set.mem_prod, Set.mem_Icc] at hp hq
    simp only [add_right_inj] at hpq
    have hlogpos : 0 < Real.log R - Real.log r := by
      have hlt : Real.log r < Real.log R := Real.log_lt_log hr hrR
      linarith
    have hpiPos : (0 : ℝ) < Real.pi := Real.pi_pos
    -- Radial part: taking norms forces the real parts of the exponents to agree, hence `p.1 = q.1`.
    have hnorm : Real.exp (Real.log r + p.1 * (Real.log R - Real.log r))
        = Real.exp (Real.log r + q.1 * (Real.log R - Real.log r)) := by
      have hcong := congrArg (fun z : ℂ => ‖z‖) hpq
      simp only [Complex.norm_exp, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
        add_zero] at hcong
      exact hcong
    have haeq : Real.log r + p.1 * (Real.log R - Real.log r)
        = Real.log r + q.1 * (Real.log R - Real.log r) := Real.exp_eq_exp.mp hnorm
    have hp1 : p.1 = q.1 :=
      mul_right_cancel₀ (ne_of_gt hlogpos) (by linarith)
    -- Angular part: `exp_eq_exp_iff_exists_int` with the `< 2π` window forces `p.2 = q.2`.
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hpq
    have himeq : Real.pi * p.2 = Real.pi * q.2 + n * (2 * Real.pi) := by
      have hnim := congrArg Complex.im hn
      simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
        Complex.intCast_re, Complex.intCast_im] at hnim
      linarith [hnim]
    have hbp : 0 ≤ Real.pi * p.2 ∧ Real.pi * p.2 ≤ Real.pi := by
      refine ⟨mul_nonneg hpiPos.le hp.2.1, ?_⟩
      nlinarith [hp.2.1, hp.2.2, hpiPos]
    have hbq : 0 ≤ Real.pi * q.2 ∧ Real.pi * q.2 ≤ Real.pi := by
      refine ⟨mul_nonneg hpiPos.le hq.2.1, ?_⟩
      nlinarith [hq.2.1, hq.2.2, hpiPos]
    have hn0 : n = 0 := by
      by_contra hne
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        have hone : (1 : ℤ) ≤ |n| := Int.one_le_abs (by simpa using hne)
        exact_mod_cast hone
      have habs : (2 * Real.pi) ≤ |(n : ℝ) * (2 * Real.pi)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        nlinarith [hpiPos, hn1]
      have hgap : |(n : ℝ) * (2 * Real.pi)| ≤ Real.pi := by
        have heq : (n : ℝ) * (2 * Real.pi) = Real.pi * p.2 - Real.pi * q.2 := by linarith [himeq]
        rw [heq, abs_sub_le_iff]
        exact ⟨by linarith [hbp.2, hbq.1], by linarith [hbq.2, hbp.1]⟩
      linarith [habs, hgap, hpiPos]
    have hbeq : Real.pi * p.2 = Real.pi * q.2 := by rw [himeq, hn0]; simp
    have hp2 : p.2 = q.2 := mul_left_cancel₀ (ne_of_gt hpiPos) hbeq
    exact Prod.ext hp1 hp2

/-- The parametrizing map of the exponential annulus quadrilateral. -/
theorem Quadrilateral.ofRoundAnnulus_toFun {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (p : ℝ × ℝ) : (Quadrilateral.ofRoundAnnulus z₀ hr hrR).toFun p
      = z₀ + Complex.exp (Complex.ofReal (Real.log r + p.1 * (Real.log R - Real.log r))
        + Complex.I * Complex.ofReal (Real.pi * p.2)) := rfl

/-- **The radius of a point of the exponential annulus quadrilateral.** For any `p` the distance
from `z₀` to `(ofRoundAnnulus z₀ hr hrR).toFun p` is `exp (log r + p.1·(log R − log r))`. -/
theorem Quadrilateral.dist_ofRoundAnnulus_toFun {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (p : ℝ × ℝ) : dist ((Quadrilateral.ofRoundAnnulus z₀ hr hrR).toFun p) z₀
      = Real.exp (Real.log r + p.1 * (Real.log R - Real.log r)) := by
  rw [Quadrilateral.ofRoundAnnulus_toFun hr hrR, dist_eq_norm, add_sub_cancel_left,
    Complex.norm_exp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

/-- **The left side of the exponential annulus quadrilateral lies on the inner circle.** At
`p.1 = 0` the radius is `exp (log r) = r`, so every point of the left side has distance `r` from
`z₀`. -/
theorem Quadrilateral.ofRoundAnnulus_leftSide_subset {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (Quadrilateral.ofRoundAnnulus z₀ hr hrR).leftSide ⊆ innerCircle z₀ r := by
  rintro w ⟨p, hp, rfl⟩
  simp only [Set.mem_prod, Set.mem_singleton_iff] at hp
  simp only [innerCircle, Set.mem_ofPred_eq, Quadrilateral.dist_ofRoundAnnulus_toFun hr hrR, hp.1]
  rw [show Real.log r + (0 : ℝ) * (Real.log R - Real.log r) = Real.log r by ring, Real.exp_log hr]

/-- **The right side of the exponential annulus quadrilateral lies on the outer circle.** At
`p.1 = 1` the radius is `exp (log R) = R`, so every point of the right side has distance `R` from
`z₀`. -/
theorem Quadrilateral.ofRoundAnnulus_rightSide_subset {z₀ : ℂ} {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) : (Quadrilateral.ofRoundAnnulus z₀ hr hrR).rightSide ⊆ outerCircle z₀ R := by
  rintro w ⟨p, hp, rfl⟩
  simp only [Set.mem_prod, Set.mem_singleton_iff] at hp
  simp only [outerCircle, Set.mem_ofPred_eq, Quadrilateral.dist_ofRoundAnnulus_toFun hr hrR, hp.1]
  rw [show Real.log r + (1 : ℝ) * (Real.log R - Real.log r) = Real.log R by ring,
    Real.exp_log (lt_trans hr hrR)]

/-- **The image of the exponential annulus quadrilateral sits in the closed round annulus.** For
`p ∈ unitSquare` the radius `exp (log r + p.1·(log R − log r))` lies in `[r, R]`. -/
theorem Quadrilateral.ofRoundAnnulus_image_dist {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∀ w ∈ (Quadrilateral.ofRoundAnnulus z₀ hr hrR).image, r ≤ dist w z₀ ∧ dist w z₀ ≤ R := by
  rintro w ⟨p, hp, rfl⟩
  simp only [unitSquare, Set.mem_prod, Set.mem_Icc] at hp
  have hlogpos : 0 < Real.log R - Real.log r := by
    have : Real.log r < Real.log R := Real.log_lt_log hr hrR
    linarith
  rw [Quadrilateral.dist_ofRoundAnnulus_toFun hr hrR]
  refine ⟨?_, ?_⟩
  · calc r = Real.exp (Real.log r) := (Real.exp_log hr).symm
      _ ≤ Real.exp (Real.log r + p.1 * (Real.log R - Real.log r)) := by
          apply Real.exp_le_exp.mpr; nlinarith [hp.1.1, hlogpos]
  · calc Real.exp (Real.log r + p.1 * (Real.log R - Real.log r))
        ≤ Real.exp (Real.log R) := by
          apply Real.exp_le_exp.mpr; nlinarith [hp.1.2, hlogpos]
      _ = R := Real.exp_log (lt_trans hr hrR)

/-- **Admissibility of the radial density for the exponential annulus quadrilateral.** Every curve
of `Q.curveFamily`, where `Q = ofRoundAnnulus z₀ hr hrR`, starts on the inner circle, ends on the
outer circle, and stays in the closed annulus, so along it the radial density sweeps the radial
range `[r, R]` and has arc-length line integral at least `1`. At interior times where the curve
touches a boundary circle the log-radius attains an extreme value, hence has vanishing derivative,
so the pointwise energy bound still holds there. -/
theorem Quadrilateral.isAdmissibleDensity_radialDensity_ofRoundAnnulus {z₀ : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    IsAdmissibleDensity (radialDensity z₀ r R)
      (Quadrilateral.ofRoundAnnulus z₀ hr hrR).curveFamily := by
  set L := Real.log (R / r) with hL
  have hRr1 : 1 < R / r := (one_lt_div hr).mpr hrR
  have hLpos : 0 < L := Real.log_pos hRr1
  -- The shifted-norm map `w ↦ ‖w - z₀‖` is 1-Lipschitz.
  have hLipShift : LipschitzWith 1 (fun w : ℂ => ‖w - z₀‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    calc |‖x - z₀‖ - ‖y - z₀‖| ≤ ‖(x - z₀) - (y - z₀)‖ := abs_norm_sub_norm_le _ _
      _ = dist x y := by rw [sub_sub_sub_cancel_right, dist_eq_norm]
  have lipComp_ac : ∀ {F : ℝ → ℂ} {K : NNReal},
      LipschitzWith K (fun w : ℂ => ‖w - z₀‖) → ∀ {a b : ℝ},
      AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun t => ‖F t - z₀‖) a b := by
    intro F K hl a b hF
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (‖F (E.2 i).1 - z₀‖) (‖F (E.2 i).2 - z₀‖)
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  have lipOnComp_ac : ∀ {F : ℝ → ℝ} {l : ℝ → ℝ} {K : NNReal} {s : Set ℝ},
      LipschitzOnWith K l s → ∀ {a b : ℝ}, AbsolutelyContinuousOnInterval F a b →
      (∀ t ∈ Set.uIcc a b, F t ∈ s) →
      AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
    intro F l K s hl a b hF hmaps
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    have hmem : ∀ i ∈ Finset.range E.1,
        (E.2 i).1 ∈ Set.uIcc a b ∧ (E.2 i).2 ∈ Set.uIcc a b := fun i hi => hE.1 i hi
    calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hl.dist_le_mul _ (hmaps _ (hmem i hi).1) _ (hmaps _ (hmem i hi).2)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  have norm_deriv_norm_le : ∀ {γ : ℝ → ℂ} {t : ℝ},
      HasDerivAt γ (deriv γ t) t →
      HasDerivAt (fun s => ‖γ s - z₀‖) (deriv (fun s => ‖γ s - z₀‖) t) t →
      |deriv (fun s => ‖γ s - z₀‖) t| ≤ ‖deriv γ t‖ := by
    intro γ t hγ hu
    rw [← Real.norm_eq_abs]
    have htu := hu.tendsto_slope
    have htγ := hγ.tendsto_slope
    have htu' : Filter.Tendsto (fun s => ‖slope (fun s => ‖γ s - z₀‖) t s‖) (𝓝[≠] t)
        (𝓝 ‖deriv (fun s => ‖γ s - z₀‖) t‖) := (continuous_norm.tendsto _).comp htu
    have htγ' : Filter.Tendsto (fun s => ‖slope γ t s‖) (𝓝[≠] t) (𝓝 ‖deriv γ t‖) :=
      (continuous_norm.tendsto _).comp htγ
    refine le_of_tendsto_of_tendsto htu' htγ' ?_
    filter_upwards with s
    rw [slope_def_module, slope_def_module, norm_smul, norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hsub : ‖(γ s - z₀) - (γ t - z₀)‖ = ‖γ s - γ t‖ := by rw [sub_sub_sub_cancel_right]
    simpa [hsub] using abs_norm_sub_norm_le (γ s - z₀) (γ t - z₀)
  refine ⟨?_, ?_⟩
  · unfold radialDensity
    apply Measurable.indicator _ ?_
    · apply ENNReal.measurable_ofReal.comp
      apply measurable_const.div
      exact ((continuous_id.sub continuous_const).norm.measurable).mul measurable_const
    · have h1 : IsOpen {z : ℂ | r < dist z z₀} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have h2 : IsOpen {z : ℂ | dist z z₀ < R} :=
        isOpen_lt (continuous_id.dist continuous_const) continuous_const
      exact (h1.inter h2).measurableSet
  · rintro γ ⟨_, hac, h0, h1, hsub⟩
    set u : ℝ → ℝ := fun t => ‖γ t - z₀‖ with hu
    have hu0 : u 0 = r := by
      have hmem := Quadrilateral.ofRoundAnnulus_leftSide_subset hr hrR h0
      simp only [innerCircle, Set.mem_ofPred_eq, dist_eq_norm] at hmem
      simp only [hu]; exact hmem
    have hu1 : u 1 = R := by
      have hmem := Quadrilateral.ofRoundAnnulus_rightSide_subset hr hrR h1
      simp only [outerCircle, Set.mem_ofPred_eq, dist_eq_norm] at hmem
      simp only [hu]; exact hmem
    have hubound : ∀ t ∈ Set.Icc (0 : ℝ) 1, r ≤ u t ∧ u t ≤ R := by
      intro t ht
      have hd := Quadrilateral.ofRoundAnnulus_image_dist hr hrR (γ t) (hsub t ht)
      simp only [dist_eq_norm] at hd
      simp only [hu]; exact hd
    have huAC : AbsolutelyContinuousOnInterval u 0 1 := lipComp_ac hLipShift hac
    have humaps : ∀ t ∈ Set.uIcc (0 : ℝ) 1, u t ∈ Set.Icc r R := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact ⟨(hubound t ht).1, (hubound t ht).2⟩
    have hlogLip : LipschitzOnWith (NNReal.mk (1/r) (by positivity)) Real.log (Set.Icc r R) := by
      apply (convex_Icc r R).lipschitzOnWith_of_nnnorm_deriv_le
      · intro x hx
        rw [Set.mem_Icc] at hx
        exact Real.differentiableAt_log (lt_of_lt_of_le hr hx.1).ne'
      · intro x hx
        rw [Set.mem_Icc] at hx
        have hx0 : 0 < x := lt_of_lt_of_le hr hx.1
        rw [Real.deriv_log, ← NNReal.coe_le_coe]
        simp only [coe_nnnorm, Real.norm_eq_abs]
        change |x⁻¹| ≤ 1 / r
        rw [abs_of_pos (by positivity), one_div]
        exact inv_anti₀ hr hx.1
    set v : ℝ → ℝ := fun t => Real.log (u t) with hv
    have hvAC : AbsolutelyContinuousOnInterval v 0 1 := lipOnComp_ac hlogLip huAC humaps
    have hv0 : v 0 = Real.log r := by rw [hv]; simp [hu0]
    have hv1 : v 1 = Real.log R := by rw [hv]; simp [hu1]
    have hvbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.log r ≤ v t ∧ v t ≤ Real.log R := by
      intro t ht
      have hb := hubound t ht
      have hut0 : 0 < u t := lt_of_lt_of_le hr hb.1
      exact ⟨Real.log_le_log hr hb.1, Real.log_le_log hut0 hb.2⟩
    have hγdiff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → DifferentiableAt ℝ γ t :=
      hac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
    have hudiff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → DifferentiableAt ℝ u t :=
      huAC.ae_differentiableAt
    have hIccIoo : (volume.restrict (Set.Icc (0 : ℝ) 1)) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
      Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm
    have hline : arcLengthLineIntegral (radialDensity z₀ r R) γ
        = ∫⁻ t in Set.Ioo (0 : ℝ) 1, radialDensity z₀ r R (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      unfold arcLengthLineIntegral
      rw [hIccIoo]
    rw [hline]
    have hFTC : ∫ t in (0 : ℝ)..1, deriv v t = L := by
      rw [hvAC.integral_deriv_eq_sub, hv1, hv0, hL,
        Real.log_div (ne_of_gt (lt_trans hr hrR)) hr.ne']
    have hvint : IntervalIntegrable (deriv v) volume 0 1 := hvAC.intervalIntegrable_deriv
    have hvintOoc : IntegrableOn (deriv v) (Set.Ioo (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hvint
    have hvabsintOoc : IntegrableOn (fun t => |deriv v t|) (Set.Ioo (0 : ℝ) 1) volume :=
      hvintOoc.abs
    have hpoint : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        ENNReal.ofReal (1 / L) * ENNReal.ofReal |deriv v t|
          ≤ radialDensity z₀ r R (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hγdiff, hudiff] with t htγ htu
      intro htmem
      have htuIcc : t ∈ Set.uIcc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le zero_le_one]; exact Set.Ioo_subset_Icc_self htmem
      have hγD : DifferentiableAt ℝ γ t := htγ htuIcc
      have huD : DifferentiableAt ℝ u t := htu htuIcc
      have hut_pos : 0 < u t := lt_of_lt_of_le hr (hubound t (Set.Ioo_subset_Icc_self htmem)).1
      have hdu_le : |deriv u t| ≤ ‖deriv γ t‖ :=
        norm_deriv_norm_le hγD.hasDerivAt huD.hasDerivAt
      have hvderiv : deriv v t = deriv u t / u t := by
        have hd : HasDerivAt v (deriv u t / u t) t := by
          have := huD.hasDerivAt.log (by rw [hu] at hut_pos ⊢; exact hut_pos.ne')
          simpa [hv, hu] using this
        exact hd.deriv
      by_cases hann : γ t ∈ RoundAnnulus z₀ r R
      · -- Interior point: the density is positive and the standard bound applies.
        have hrhoval : radialDensity z₀ r R (γ t) = ENNReal.ofReal (1 / (u t * L)) := by
          simp only [radialDensity, Set.indicator_of_mem hann, hu, hL]
        rw [hrhoval, hvderiv]
        have key1 : ENNReal.ofReal (1 / L) * ENNReal.ofReal |deriv u t / u t|
            = ENNReal.ofReal (1 / (u t * L)) * ENNReal.ofReal |deriv u t| := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [abs_div, abs_of_pos hut_pos]
          field_simp
        rw [key1]
        gcongr
        rw [show (‖deriv γ t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv γ t‖ from by
          rw [ofReal_norm, enorm_eq_nnnorm]]
        exact ENNReal.ofReal_le_ofReal hdu_le
      · -- Boundary point: `v` attains an extreme value at `t`, so `deriv v t = 0`.
        have hvderiv0 : deriv v t = 0 := by
          have hIoonhds : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 t := isOpen_Ioo.mem_nhds htmem
          have hut_mem : u t = r ∨ u t = R := by
            have hb := hubound t (Set.Ioo_subset_Icc_self htmem)
            by_contra hcon
            rw [not_or] at hcon
            refine hann ⟨?_, ?_⟩
            · rw [dist_eq_norm]; exact lt_of_le_of_ne hb.1 (Ne.symm hcon.1)
            · rw [dist_eq_norm]; exact lt_of_le_of_ne hb.2 hcon.2
          have hvD : HasDerivAt v (deriv v t) t := by
            have hd : HasDerivAt v (deriv u t / u t) t := by
              have := huD.hasDerivAt.log (by rw [hu] at hut_pos ⊢; exact hut_pos.ne')
              simpa [hv, hu] using this
            rw [hvderiv]; exact hd
          rcases hut_mem with hmin | hmax
          · have hvt : v t = Real.log r := by simp only [hv, hmin]
            have hlocmin : IsLocalMin v t := by
              rw [IsLocalMin, IsMinFilter]
              filter_upwards [hIoonhds] with s hs
              rw [hvt]; exact (hvbound s (Set.Ioo_subset_Icc_self hs)).1
            exact hlocmin.hasDerivAt_eq_zero hvD
          · have hvt : v t = Real.log R := by simp only [hv, hmax]
            have hlocmax : IsLocalMax v t := by
              rw [IsLocalMax, IsMaxFilter]
              filter_upwards [hIoonhds] with s hs
              rw [hvt]; exact (hvbound s (Set.Ioo_subset_Icc_self hs)).2
            exact hlocmax.hasDerivAt_eq_zero hvD
        rw [hvderiv0]
        simp
    calc (1 : ℝ≥0∞)
        = ENNReal.ofReal (1 / L) * ENNReal.ofReal L := by
          rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hLpos.ne',
            ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (1 / L) * ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv v t| := by
          gcongr ?_ * ?_
          · exact le_rfl
          rw [← hFTC]
          calc ENNReal.ofReal (∫ t in (0 : ℝ)..1, deriv v t)
              ≤ ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, |deriv v t|) := by
                apply ENNReal.ofReal_le_ofReal
                rw [intervalIntegral.integral_of_le zero_le_one,
                  integral_Ioc_eq_integral_Ioo]
                apply setIntegral_mono_on hvintOoc hvabsintOoc measurableSet_Ioo
                intro x _; exact le_abs_self _
            _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv v t| := by
                rw [ofReal_integral_eq_lintegral_ofReal hvabsintOoc
                  (ae_restrict_of_forall_mem measurableSet_Ioo (fun x _ => abs_nonneg _))]
      _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / L) * ENNReal.ofReal |deriv v t| := by
          rw [lintegral_const_mul]
          exact ENNReal.measurable_ofReal.comp (_root_.continuous_abs.measurable.comp
            (measurable_deriv v))
      _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, radialDensity z₀ r R (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) :=
          lintegral_mono_ae hpoint

/-- **Modulus bound of the exponential annulus quadrilateral.** For radii `0 < r < R` the
quadrilateral `Quadrilateral.ofRoundAnnulus z₀ hr hrR`, which realizes the slit round annulus, has
modulus at most the round-annulus (ring) modulus. The radial density is admissible for its
connecting
family and has area energy equal to the ring modulus, so the modulus — an infimum over admissible
densities — is bounded by that energy. -/
theorem Quadrilateral.ofRoundAnnulus_modulus_le {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (Quadrilateral.ofRoundAnnulus z₀ hr hrR).modulus ≤ ringModulus z₀ r R := by
  rw [Quadrilateral.modulus, curveModulus]
  refine le_trans (iInf₂_le (radialDensity z₀ r R) ?_) ?_
  · exact Quadrilateral.isAdmissibleDensity_radialDensity_ofRoundAnnulus hr hrR
  · exact le_of_eq (lintegral_radialDensity_sq hr hrR)

/-- **Forward quasiconformal transport for a round annulus.** For a geometric `K`-quasiconformal map
`f`, the image under `f` of the connecting family of the exp-rectangle quadrilateral realizing the
round annulus `RoundAnnulus z₀ r R` has modulus at most `K · ringModulus z₀ r R`. This applies the
`IsQCGeometric` modulus-distortion bound to `Quadrilateral.ofRoundAnnulus` together with the modulus
bound `ofRoundAnnulus_modulus_le`. -/
theorem curveModulus_imageCurveFamily_ofRoundAnnulus_le {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    curveModulus ((Quadrilateral.ofRoundAnnulus z₀ hr hrR).imageCurveFamily f)
      ≤ ENNReal.ofReal K * ringModulus z₀ r R :=
  le_trans (hf.2.2 _) (by gcongr; exact Quadrilateral.ofRoundAnnulus_modulus_le hr hrR)

end NoWanderingDomains
