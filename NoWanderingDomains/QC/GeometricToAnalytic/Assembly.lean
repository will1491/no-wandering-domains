/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Geometric
import NoWanderingDomains.QC.Defs.Analytic
import NoWanderingDomains.QC.Defs.SensePreserving
import NoWanderingDomains.QC.LengthArea.LengthAreaInverse
import NoWanderingDomains.QC.LengthArea.ReverseLengthArea
import NoWanderingDomains.QC.LengthArea.ReverseLengthAreaEnergy
import NoWanderingDomains.QC.GeometricToAnalytic.NondegeneracyAssembly
import NoWanderingDomains.Analysis.Sobolev.AbsolutelyContinuousLines
import NoWanderingDomains.Analysis.Sobolev.Stepanov

/-!
# Geometric ⇒ analytic: the Gehring–Lehto stages

This file decomposes the hard direction of the quasiconformal equivalence —
`isQCAnalytic_of_isQCGeometric` in `QC/Equivalence.lean` — into its classical
Gehring–Lehto stages, stated here as separate lemmas. A geometric `K`-quasiconformal map
(a sense-preserving homeomorphism whose image-family modulus is `≤ K · M(Q)` for every
quadrilateral) is absolutely continuous on lines, lies in `W^{1,2}_loc`, is differentiable
almost everywhere, and satisfies a Beltrami equation with dilatation bound
`‖μ‖∞ ≤ (K − 1)/(K + 1)`.

## Stages

* `IsQCGeometric.exists_acl_weakGradient` — **reverse length–area**: the modulus bound forces
  absolute continuity on almost every horizontal and vertical line, with `L²_loc` partials.
  *(the converse of the length–area inequality)*
* `IsQCGeometric.ae_differentiableAt` — **Stepanov / Gehring–Lehto a.e. differentiability**:
  an ACL map with `L²_loc` partials is (totally) differentiable almost everywhere. Rademacher
  does not apply (the map is not Lipschitz); this is the Stepanov refinement.
  *(approximate differentiability is absent from Mathlib)*
* `IsQCGeometric.exists_beltrami` — **dilatation bound**: at almost every point the pointwise
  dilatation `‖∂̄f / ∂f‖` is `≤ (K − 1)/(K + 1)`, packaged as a `BeltramiCoeff`.

These stages assemble (with `SensePreserving.isHomeomorph`, `memWklocP_one_of_acl`,
`SensePreserving.ae_det_pos`) into `isQCAnalytic_of_isQCGeometric`.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace NoWanderingDomains

/-- **Reverse length–area / Gehring–Lehto infinitesimal data (the single genuine GMT
residual of the geometric ⇒ analytic direction).**

For a geometric `K`-quasiconformal map `f` the modulus bound
`M(f(Q)) ≤ K · M(Q)` on every quadrilateral forces, classically, the entire *infinitesimal*
structure of `f` at once:

* `f` is (totally, real-)differentiable at almost every point;
* its Jacobian is positive almost everywhere;
* the pointwise dilatation bound `‖Df w‖² ≤ K · det (Df w)` holds almost everywhere;
* the pointwise partials `w ↦ (Df w) 1`, `w ↦ (Df w) I` are the **weak (distributional)**
  derivatives of `f` (equivalently, the distributional gradient of `f` has *no singular
  part*, i.e. `f ∈ W^{1,1}_loc` with these partials).

This is the classical **reverse length–area theorem**. In the standard proof
one first runs the length–area inequality: for an axis rectangle `R = (a,b)×(s,t)` the
horizontal-segment family has modulus `(t−s)/(b−a)` from below
(`lengthArea_modulus_lower_bound`), and combined with the geometric upper bound
`M(f(R)) ≤ K·M(R)` and a Cauchy–Schwarz / Fubini estimate gives the energy inequality
`∫_{y∈[s,t]} ℓ_f(y)² dy ≤ K · area(f(R))`, where `ℓ_f(y)` is the length (total variation) of
the image slice `x ↦ f⟨x,y⟩`. Hence a.e. slice is BV with `L²_loc` `x`-partial, and
symmetrically for `y`. The genuinely two-dimensional **"no singular part" step** (a.e. slice
is *absolutely continuous*, not merely BV) is the Banach–Zaretsky / Federer area-formula core:
the swept image area `area(f(·))` is countably additive and absolutely continuous, which
forces equality in the length–area estimate and rules out a slice singular part. From the
slice-AC and the energy bound the a.e. differentiability and the pointwise dilatation bound
follow by the Gehring–Lehto / Stepanov refinement.

## Why this is the tight, irreducible residual

The conclusion bundles *all four* infinitesimal facts because for a **purely geometric** map
they are not separately available: a.e. differentiability is a *conclusion* of the
geometric ⇒ analytic direction (the orientation hypothesis `SensePreserving` is purely
topological and carries no differentiability — see the `IsQCGeometric` docstring), so it
cannot be assumed in order to *define* the partials, and the pointwise dilatation bound is a
downstream Gehring–Lehto consequence of the very slice-AC it would help establish. The four
facts emerge **together** from the length–area / no-singular-part analysis; separating any one
of them out would require the others as hypotheses, so a single bundled residual is the
honest granularity. Its mathematical content is **exactly** the same "no singular part" claim
stated on the analytic side as `IsQCAnalytic.inverse_reverseLengthArea_weakGradient`
(`QC/InverseQC/`), specialised to the inverse map: closing either in full closes both.

## Status: Mathlib/repo-absent

The "no singular part" core requires the Federer co-area / multiplicity area formula in its
*non-injective* (`≤`) direction together with the variation lower bound `Var ≥ ∫|deriv|`, plus
approximate differentiability and the planar Lusin-(N) bridge — none of which are in Mathlib
(`QC/Foundations/MultiplicityAreaFormula.lean` proves the fibered Banach-indicatrix bound but the
area
*equality* coupling is absent). It is the sole remaining node of this stage.

## Soundness (shear sanity check)

The conclusion is **false** for the area-preserving singular shear
`g⟨x,y⟩ = x + i·(y + s x)` (`s` continuous strictly increasing singular, e.g. Minkowski `?`):
`g` is an injective continuous a.e.-differentiable measure-preserving map with `Dg = id`
a.e. — so it satisfies the first three facts pointwise — **yet** its imaginary slice
`x ↦ y + s x` is singular (not AC), so its true distributional `x`-derivative of `.im` is the
singular measure `ds`, not the a.e.-pointwise `0`; the weak-gradient fact fails. The shear is
*not* geometrically `K`-quasiconformal (its quadrilateral moduli are not boundedly distorted —
the singular shear blows up the modulus of thin vertical quadrilaterals), so the hypothesis
`hf : IsQCGeometric f K` is load-bearing and the statement is sound. -/
theorem IsQCGeometric.reverseLengthArea_data {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    (∀ᵐ w : ℂ, DifferentiableAt ℝ f w) ∧
    (∀ᵐ w : ℂ, 0 < (fderiv ℝ f w).det) ∧
    (∀ᵐ w : ℂ, ‖fderiv ℝ f w‖ ^ 2 ≤ K * (fderiv ℝ f w).det) ∧
    HasWeakDirDeriv 1 (fun w => (fderiv ℝ f w) 1) f Set.univ ∧
    HasWeakDirDeriv Complex.I (fun w => (fderiv ℝ f w) Complex.I) f Set.univ := by
  classical
  have hfcont : Continuous f := hf.2.1.isHomeomorph.continuous
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hf.1
  have hhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  -- (1) Almost-everywhere total differentiability via the **proven Grötzsch-free Gehring–Lehto
  -- theorem**: the forward reverse length–area residual `exists_acl_memLp_sliceGradient` gives an
  -- `L²_loc` ACL gradient (`f ∈ W^{1,2}_loc`), and `ae_differentiableAt_of_W12loc_homeomorph`
  -- upgrades a `W^{1,2}_loc` homeomorphism to a.e. differentiability — with no quasiconformal
  -- roundness and no Grötzsch symmetrization input.
  have hdiff : ∀ᵐ w : ℂ, DifferentiableAt ℝ f w := hf.ae_differentiableAt_gehringLehto
  -- (2),(3) The pointwise dilatation bound and nondegeneracy of the Jacobian, derived **directly**
  -- from the Grötzsch-free `infinitesimal_dilatation` filtered with the a.e.-differentiability
  -- `hdiff` (rather than via the former roundness-based dilatation route).
  have hdil : ∀ᵐ w : ℂ,
      ‖fderiv ℝ f w‖ ^ 2 ≤ K * (fderiv ℝ f w).det ∧ (fderiv ℝ f w).det ≠ 0 := by
    filter_upwards [hdiff, hf.infinitesimal_dilatation] with w hd himp
    obtain ⟨hdet, hb⟩ := himp hd
    exact ⟨hb, hdet⟩
  -- (3) The dilatation conjunct.
  have hdil3 : ∀ᵐ w : ℂ, ‖fderiv ℝ f w‖ ^ 2 ≤ K * (fderiv ℝ f w).det := by
    filter_upwards [hdil] with w hw using hw.1
  -- (2) Positivity of the Jacobian from sense-preservation and nondegeneracy.
  have hdetpos : ∀ᵐ w : ℂ, 0 < (fderiv ℝ f w).det := by
    refine hf.2.1.ae_det_pos ?_
    filter_upwards [hdiff, hdil] with w hd hw using ⟨hd, hw.2⟩
  -- The forward slice-AC data, taken **Grötzsch-free** from the energy residual
  -- `exists_acl_memLp_sliceGradient` (its `ACLHorizontal`/`ACLVertical` conjuncts bundle slice
  -- absolute continuity). NOTE: we do *not* use the former slice-AC route (through slice
  -- bounded variation and the no-singular-part step), which still called the quasiconformal
  -- roundness lemmas and reintroduced the Grötzsch symmetrization input.
  obtain ⟨gx', gy', hAClx, hACly, _, _⟩ := hf.exists_acl_memLp_sliceGradient
  have hacx : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => f ⟨x, y⟩) a b := by
    filter_upwards [hAClx] with y hy using hy.1
  have hacy : ∀ᵐ x : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun y : ℝ => f ⟨x, y⟩) a b := by
    filter_upwards [hACly] with x hx using hx.1
  -- (4),(5) The `L²_loc` `fderiv`-partials, derived **Grötzsch-free** from the pointwise dilatation
  -- bound via `memLpLocOn_inverse_partial_of_dilatation` applied to `f` itself, replacing the
  -- roundness route `memLpLocOn_partials`.
  have hL2x : MemLpLocOn (fun w => (fderiv ℝ f w) 1) (2 : ℝ≥0∞) Set.univ :=
    memLpLocOn_inverse_partial_of_dilatation hKpos hhomeo hdiff hdetpos hdil3 1
  have hL2y : MemLpLocOn (fun w => (fderiv ℝ f w) Complex.I) (2 : ℝ≥0∞) Set.univ :=
    memLpLocOn_inverse_partial_of_dilatation hKpos hhomeo hdiff hdetpos hdil3 Complex.I
  -- `L²_loc ⟹ L¹_loc` on compacts supplies the local integrability the weak-gradient bridge needs.
  have hLIofL2 : ∀ {h : ℂ → ℂ}, MemLpLocOn h (2 : ℝ≥0∞) Set.univ → LocallyIntegrable h := by
    intro h hh
    rw [MeasureTheory.locallyIntegrable_iff]
    intro Kc hKc
    have hmem : MemLp h (2 : ℝ≥0∞) (volume.restrict Kc) := hh Kc (Set.subset_univ _) hKc
    have : IsFiniteMeasure (volume.restrict Kc) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top
    exact (hmem.mono_exponent (by norm_num)).integrable (le_refl 1)
  have hgxLI : LocallyIntegrable (fun w => (fderiv ℝ f w) 1) := hLIofL2 hL2x
  have hgyLI : LocallyIntegrable (fun w => (fderiv ℝ f w) Complex.I) := hLIofL2 hL2y
  -- (4),(5) The two weak directional derivatives, via the proven slice-AC ⟹ weak-gradient bridge.
  have hwg : HasWeakGradient (fun w => (fderiv ℝ f w) 1)
      (fun w => (fderiv ℝ f w) Complex.I) f Set.univ :=
    hasWeakGradient_of_aeSliceAC hfcont hdiff hgxLI hgyLI hacx hacy
  exact ⟨hdiff, hdetpos, hdil3, hwg.1, hwg.2⟩

/-- **Reverse length–area (geometric ⇒ ACL).** A geometric `K`-quasiconformal map is
absolutely continuous on almost every horizontal and vertical line, with `x`- and
`y`-partials that are locally `L²`. This is the converse of the length–area inequality: the
modulus bound `M(f(Q)) ≤ K · M(Q)` on rectangles forces, by a Fubini/length–area argument,
absolute continuity of the line slices together with the square-integrable energy bound.

The genuine reverse-length-area / "no singular part" content is the single residual
`IsQCGeometric.reverseLengthArea_data`; here it is packaged into the `ACL` + `L²_loc` shape by
the fully proven keystone `acl_weakGradient_of_qcInverse` (`QC/LengthArea/LengthAreaInverse.lean`),
whose
energy half (`memLpLocOn_inverse_partial_of_dilatation`) derives the square-integrable bound on
the partials directly from the pointwise dilatation bound `‖Df‖² ≤ K · det (Df)`. -/
theorem IsQCGeometric.exists_acl_weakGradient {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∃ gx gy : ℂ → ℂ, ACLHorizontal f gx ∧ ACLVertical f gy ∧
      MemLpLocOn gx (2 : ℝ≥0∞) Set.univ ∧ MemLpLocOn gy (2 : ℝ≥0∞) Set.univ := by
  -- `f` is a homeomorphism and `K` is positive.
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hf.1
  have hhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  -- The single genuine reverse-length-area / Gehring–Lehto residual supplies the infinitesimal
  -- data (a.e. differentiability, positive Jacobian, pointwise dilatation bound, weak gradient).
  obtain ⟨hdiff, hdetpos, hdil, hweakx, hweaky⟩ := hf.reverseLengthArea_data
  -- The fully proven keystone packages this into the ACL + `L²_loc` conclusion, deriving the
  -- square-integrable energy bound on the partials from the pointwise dilatation bound.
  exact acl_weakGradient_of_qcInverse hKpos hhomeo hdiff hdetpos hdil hweakx hweaky

/-- **Stepanov / Gehring–Lehto a.e. differentiability.** A geometric `K`-quasiconformal map
is (totally, real-)differentiable at almost every point. The map is absolutely continuous on
lines with `L²_loc` partials (`exists_acl_weakGradient`); the Stepanov theorem upgrades this
to total differentiability a.e. (Rademacher is inapplicable — the map need not be Lipschitz). -/
theorem IsQCGeometric.ae_differentiableAt {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ᵐ z : ℂ, DifferentiableAt ℝ f z :=
  hf.reverseLengthArea_data.1

/-- **Dilatation bound (geometric ⇒ Beltrami).** A geometric `K`-quasiconformal map satisfies
a Beltrami equation `∂̄f = b.μ · ∂f` almost everywhere with a coefficient of essential norm at
most `(K − 1)/(K + 1)`. At almost every point of differentiability the infinitesimal modulus
distortion is `≤ K`, which is exactly the pointwise dilatation bound
`‖∂̄f / ∂f‖ ≤ (K − 1)/(K + 1)`; measurability and the essential-norm bound package it as a
`BeltramiCoeff`. -/
theorem IsQCGeometric.exists_beltrami {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    (hf : IsQCGeometric f K) :
    ∃ b : BeltramiCoeff, b.normInf ≤ (K - 1) / (K + 1) ∧
      ∀ᵐ z : ℂ, dzbar f z = b.μ z * dz f z := by
  classical
  -- STEP 0 — the infinitesimal data from the reverse length–area residual.
  obtain ⟨hdiff, hdetpos, hdil, -, -⟩ := hf.reverseLengthArea_data
  -- STEP 1 — scalar bookkeeping.
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  set c : ℝ := (K - 1) / (K + 1) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]; apply div_nonneg <;> linarith
  have hc1 : c < 1 := by
    rw [hc, div_lt_one hK1]; linarith
  -- STEP 2 — the clamped Beltrami coefficient.
  set raw : ℂ → ℂ := fun w => dzbar f w / dz f w with hraw
  set μ' : ℂ → ℂ := fun w => if ‖raw w‖ ≤ c then raw w else 0 with hμ'
  -- STEP 3 — measurability.
  have hdzf_meas : Measurable (fun w : ℂ => dz f w) := by
    have h1 : Measurable (fun w : ℂ => (fderiv ℝ f w) 1) := measurable_fderiv_apply_const ℝ f 1
    have h2 : Measurable (fun w : ℂ => (fderiv ℝ f w) Complex.I) :=
      measurable_fderiv_apply_const ℝ f Complex.I
    simpa only [dz] using! (measurable_const.mul (h1.sub (measurable_const.mul h2)))
  have hdzbarf_meas : Measurable (fun w : ℂ => dzbar f w) := by
    have h1 : Measurable (fun w : ℂ => (fderiv ℝ f w) 1) := measurable_fderiv_apply_const ℝ f 1
    have h2 : Measurable (fun w : ℂ => (fderiv ℝ f w) Complex.I) :=
      measurable_fderiv_apply_const ℝ f Complex.I
    simpa only [dzbar] using! (measurable_const.mul (h1.add (measurable_const.mul h2)))
  have hraw_meas : Measurable raw := hdzbarf_meas.div hdzf_meas
  have hμ'_meas : Measurable μ' :=
    Measurable.ite (measurableSet_le hraw_meas.norm measurable_const) hraw_meas measurable_const
  -- STEP 4 — pointwise bound `‖μ' w‖ ≤ c`.
  have hμ'_le : ∀ w, ‖μ' w‖ ≤ c := by
    intro w
    rw [hμ']
    by_cases h : ‖raw w‖ ≤ c
    · simp [h]
    · simp [h, hc0]
  -- STEP 5 — essential-sup bound.
  have hμ'_bound : eLpNormEssSup μ' volume < 1 := by
    refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hμ'_le)) ?_
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0).mpr hc1
  -- STEP 6 — assemble the coefficient.
  refine ⟨⟨μ', hμ'_meas, hμ'_bound⟩, ?_, ?_⟩
  · -- STEP 7 — `b.normInf ≤ c`.
    have hbnd : eLpNormEssSup μ' volume ≤ ENNReal.ofReal c :=
      eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hμ'_le)
    have h1 : (eLpNormEssSup μ' volume).toReal ≤ (ENNReal.ofReal c).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd
    rw [ENNReal.toReal_ofReal hc0] at h1
    simpa only [BeltramiCoeff.normInf] using h1
  · -- STEP 8 — the Beltrami relation at a.e. `z`.
    filter_upwards [hdiff, hdetpos, hdil] with z _ hdz hdl
    -- Abbreviations for the two Wirtinger values and their norms.
    set p : ℝ := ‖dz f z‖ with hpdef
    set q : ℝ := ‖dzbar f z‖ with hqdef
    have hp0 : 0 ≤ p := norm_nonneg _
    have hq0 : 0 ≤ q := norm_nonneg _
    -- The two Wirtinger identities.
    have hdet : (fderiv ℝ f z).det = p ^ 2 - q ^ 2 := det_fderiv_eq_wirtinger f z
    have hop : ‖fderiv ℝ f z‖ = p + q := opNorm_fderiv_eq_wirtinger f z
    -- From the positive Jacobian: `p² − q² > 0`, hence `q < p` and `0 < p`.
    rw [hdet] at hdz
    have hqltp : q < p := by nlinarith [hp0, hq0]
    have hppos : 0 < p := lt_of_le_of_lt hq0 hqltp
    have hpqpos : 0 < p + q := by linarith
    -- `dz f z ≠ 0` since `‖dz f z‖ = p > 0`.
    have hdzne : dz f z ≠ 0 := by
      rw [← norm_pos_iff]; exact hppos
    -- REVERSE DILATATION ALGEBRA: from `‖Df‖² ≤ K · det`, i.e. `(p+q)² ≤ K·(p²−q²)`,
    -- derive `q ≤ c · p`.
    rw [hop, hdet] at hdl
    have hqcp : q ≤ c * p := by
      -- `(p+q)² ≤ K(p−q)(p+q)` and `p+q>0` give `p+q ≤ K(p−q)`, hence `(K+1)q ≤ (K−1)p`.
      have hstep : (K + 1) * q ≤ (K - 1) * p := by nlinarith [hpqpos, hdl]
      rw [hc]
      rw [div_mul_eq_mul_div, le_div_iff₀ hK1]
      nlinarith [hstep]
    -- Hence `‖raw z‖ = q / p ≤ c`, so the clamp returns the raw quotient.
    have hraww : ‖raw z‖ ≤ c := by
      have hrawval : raw z = dzbar f z / dz f z := by rw [hraw]
      rw [hrawval, norm_div, ← hpdef, ← hqdef, div_le_iff₀ hppos]
      exact hqcp
    -- Conclude `dzbar f z = μ' z · dz f z`.
    change dzbar f z = μ' z * dz f z
    have hμ'z : μ' z = dzbar f z / dz f z := by
      rw [hμ']; simp only [hraww, if_true]; rw [hraw]
    rw [hμ'z, div_mul_cancel₀ (dzbar f z) hdzne]

end NoWanderingDomains
