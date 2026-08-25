/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.GeometricToAnalytic.GeometricDifferentiable.Reciprocity
import NoWanderingDomains.QC.GeometricToAnalytic.LoewnerReciprocity

/-!
# Conjugate-image modulus reciprocity — assembly

The per-density length–area inequality and the conjugate-image modulus reciprocity
`square_imageCurveFamily_modulus_ge`, assembled from the planar Loewner cross-bound
`loewner_image_cross_bound_axisRect` (`QC/GeometricToAnalytic/LoewnerReciprocity.lean`)
and the Rengel finiteness witnesses (`GeometricDifferentiable/Primitives.lean`).

For a homeomorphism `f` and an axis rectangle `(a, b) × (s, t)`, every finite-energy `ρ`
admissible for the image crossing family `Γ` and every finite-energy `σ` admissible for the
image separating family `Γ*` satisfy `1 ≤ (∫∫ ρ²) · (∫∫ σ²)`
(`imageConjugate_lengthArea_pairwise`, below). Taking the infimum over `ρ` then `σ`, this
per-pair bound is exactly the conjugate-image reciprocity `1 ≤ M(Γ) · M(Γ*)` (via
`one_le_biInf_mul_biInf'` and the finiteness witnesses `imageCurveFamily_finiteWitness`).
This is the **easy** direction of reciprocity; no conformality or differentiability of `f`
is used.

The finite-energy hypotheses on both densities are the honest classical form of the
cross-bound (Eriksson-Bique–Poggi-Corradini take `σ ∈ L^q` in exactly the same role), and
are all the modulus reciprocity consumes: the infima defining the two moduli are attained
along finite-energy densities, courtesy of the Rengel witnesses.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal Real

namespace NoWanderingDomains

/-- **The crossing-principle cross-bound (the atomic reciprocity residual).**

For a homeomorphism `f`, an admissible finite-energy `ρ` for the image **crossing** family
of an axis rectangle and an admissible finite-energy `σ` for the conjugate image
**separating** family,

  `1 ≤ ∫∫ ρ · σ`.

This is the genuine topological/measure content of conformal-modulus reciprocity: every
crossing curve meets every
separating curve in a topological square, and the co-area pairing over the level sets of the
Beurling chain potential delivers the bound.

**Discharged by reduction** to the planar Loewner reciprocity workstream: the body is a
one-line call into `loewner_image_cross_bound_axisRect`, whose signature matches this
theorem exactly. -/
theorem imageConjugate_cross_bound {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f))
    (hρE : (∫⁻ z, (ρ z) ^ 2) ≠ ⊤) (hσE : (∫⁻ z, (σ z) ^ 2) ≠ ⊤) :
    1 ≤ ∫⁻ z, ρ z * σ z :=
  loewner_image_cross_bound_axisRect hf hab hst hρ hσ hρE hσE

/-- **The length–area cross-inequality (conformal-modulus reciprocity, energy form).**

`1 ≤ (∫∫ ρ²) · (∫∫ σ²)` for an admissible finite-energy crossing `ρ` and separating `σ` of
the conjugate image families.  Obtained from the crossing-principle cross-bound
`imageConjugate_cross_bound` (`1 ≤ ∫∫ ρσ`) via the Cauchy–Schwarz step
`one_le_energy_mul_energy_of_one_le_lintegral_mul`. -/
theorem imageConjugate_lengthArea_pairwise {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f))
    (hρE : (∫⁻ z, (ρ z) ^ 2) ≠ ⊤) (hσE : (∫⁻ z, (σ z) ^ 2) ≠ ⊤) :
    1 ≤ (∫⁻ z, (ρ z) ^ 2) * (∫⁻ z, (σ z) ^ 2) :=
  one_le_energy_mul_energy_of_one_le_lintegral_mul hρ.1 hσ.1
    (imageConjugate_cross_bound hf hab hst hρ hσ hρE hσE)

/-- **Conjugate-image modulus reciprocity.**

For a homeomorphism `f : ℂ → ℂ` and an axis *square* `S = (a, b) × (s, t)` (`b − a = t − s`), the
two conjugate **image** families of `S` — the crossing family `Γ = S.imageCurveFamily f`
(`f`-image of left ↔ right) and the separating family `Γ* = (swapped S).imageCurveFamily f`
(`f`-image of bottom ↔ top) — satisfy modulus reciprocity `1 ≤ M(Γ) · M(Γ*)`.

This is **fully reduced** to `imageConjugate_lengthArea_pairwise` (the per-density length–area
inequality; see its docstring), which bottoms out at the planar Loewner residual
`loewner_image_cross_bound_axisRect`. The reduction is
the `ℝ≥0∞` lemma `one_le_biInf_mul_biInf'` fed by the two Rengel finiteness witnesses
`imageCurveFamily_finiteWitness` (constructed from `image_axisRectQuadrilateral_volume_pos` /
`…Swap` and the disjoint-image-sides lemmas). The finite-energy guards of the pairwise bound
are exactly the guards `one_le_biInf_mul_biInf'` supplies. -/
theorem conjugateImageModulus_reciprocity {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    1 ≤ curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f)
      * curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f) := by
  obtain ⟨hdisjC, hneLC⟩ := image_axisRectQuadrilateral_sides_disjoint hf hab hst
  obtain ⟨hdisjS, hneLS⟩ := image_axisRectQuadrilateralSwap_sides_disjoint hf hab hst
  have hwitC := imageCurveFamily_finiteWitness hf (axisRectQuadrilateral a b s t hab hst)
    (image_axisRectQuadrilateral_volume_pos hf hab hst) hdisjC hneLC
  obtain ⟨ρ₀, hρ₀adm, hρ₀0, hρ₀top⟩ := hwitC
  -- the swapped family's image region equals the same rectangle, so its volume is positive too
  have hposvolS : 0 < volume (f '' (axisRectQuadrilateralSwap a b s t hab hst).image) := by
    rw [axisRectQuadrilateralSwap_image]
    exact image_axisRectQuadrilateral_volume_pos hf hab hst
  have hwitS := imageCurveFamily_finiteWitness hf (axisRectQuadrilateralSwap a b s t hab hst)
    hposvolS hdisjS hneLS
  obtain ⟨σ₀, hσ₀adm, _, hσ₀top⟩ := hwitS
  -- Apply the reduction lemma with explicit index sets and value functions, so no expensive
  -- unification of the `biInf` shape is needed.
  -- The pairwise length–area bound is needed only for finite-energy densities; the finite-energy
  -- guards `∫⁻ ρ² ≠ ⊤`, `∫⁻ σ² ≠ ⊤` are exactly the hypotheses
  -- `imageConjugate_lengthArea_pairwise` consumes.
  have hpair : ∀ ρ ∈ {ρ : ℂ → ℝ≥0∞ |
        IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f)},
      (∫⁻ z, (ρ z) ^ 2) ≠ ⊤ → ∀ σ ∈ {σ : ℂ → ℝ≥0∞ |
        IsAdmissibleDensity σ ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)},
      (∫⁻ z, (σ z) ^ 2) ≠ ⊤ → 1 ≤ (∫⁻ z, (ρ z) ^ 2) * (∫⁻ z, (σ z) ^ 2) :=
    fun ρ hρ hρE σ hσ hσE => imageConjugate_lengthArea_pairwise hf hab hst hρ hσ hρE hσE
  have hmain := one_le_biInf_mul_biInf'
    (I := {ρ : ℂ → ℝ≥0∞ |
      IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f)})
    (J := {σ : ℂ → ℝ≥0∞ |
      IsAdmissibleDensity σ ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)})
    (fun ρ => ∫⁻ z, (ρ z) ^ 2) (fun σ => ∫⁻ z, (σ z) ^ 2)
    ⟨ρ₀, hρ₀adm, hρ₀0, hρ₀top⟩ ⟨σ₀, hσ₀adm⟩ ⟨σ₀, hσ₀adm, hσ₀top⟩ hpair
  exact hmain

/-- **Modulus lower bound for the image of an axis square.**

For a geometric `K`-quasiconformal map `f` and an axis-aligned **square** `Q = (a, b) × (s, t)`
(`b − a = t − s`, so `Q` has crossing modulus `1`), the modulus of the image crossing family is at
least `1/K`:
`ENNReal.ofReal (1/K) ≤ curveModulus (Q.imageCurveFamily f)`.

## Proof (the reciprocity route)

This is **fully reduced** to `conjugateImageModulus_reciprocity` (modulus reciprocity
`M(Γ) · M(Γ*) ≥ 1` for the two conjugate image families), which bottoms out at the planar Loewner
residual `loewner_image_cross_bound_axisRect`. Writing `Γ = Q.imageCurveFamily f` (crossing) and
`Γ* = Q♯.imageCurveFamily f` for
the swapped square `Q♯` (separating), the steps are:
* `M(Γ*) ≤ K`: the geometric upper bound `hf.2.2` applied to the **swapped** square `Q♯`, whose
  modulus is `≤ (b − a)/(t − s) = 1` for a square (`axisRectSwap_modulus_upper_bound`);
* reciprocity `1 ≤ M(Γ) · M(Γ*)` (`conjugateImageModulus_reciprocity`);
* combine: `1 ≤ M(Γ) · M(Γ*) ≤ M(Γ) · K`, i.e. `1 ≤ M(Γ) · ofReal K`.

Multiplying by `ofReal (1/K)` (and cancelling) yields `M(Γ) ≥ 1/K`. All steps except
`conjugateImageModulus_reciprocity` are carried out here. -/
theorem square_imageCurveFamily_modulus_ge {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) (hsquare : b - a = t - s) :
    ENNReal.ofReal (1 / K)
      ≤ curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f) := by
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hf.1
  have hfhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  set M := curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f) with hM
  set N := curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f) with hN
  -- `M(Γ*) ≤ K`: geometric upper bound on the swapped square; its modulus is `≤ 1` (square).
  have hNK : N ≤ ENNReal.ofReal K := by
    have hmod := hf.2.2 (axisRectQuadrilateralSwap a b s t hab hst)
    have hupper : (axisRectQuadrilateralSwap a b s t hab hst).modulus ≤ 1 := by
      refine le_trans (axisRectSwap_modulus_upper_bound hab hst) ?_
      rw [hsquare, div_self (by linarith : t - s ≠ 0), ENNReal.ofReal_one]
    calc N = curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f) := hN
      _ ≤ ENNReal.ofReal K * (axisRectQuadrilateralSwap a b s t hab hst).modulus := hmod
      _ ≤ ENNReal.ofReal K * 1 := by gcongr
      _ = ENNReal.ofReal K := mul_one _
  -- Reciprocity `1 ≤ M · N`.
  have hrecip : 1 ≤ M * N := conjugateImageModulus_reciprocity hfhomeo hab hst
  -- Chain: `1 ≤ M · N ≤ M · ofReal K`.
  have hchain : (1 : ℝ≥0∞) ≤ M * ENNReal.ofReal K :=
    le_trans hrecip (by gcongr)
  -- `1 ≤ M · ofReal K`  ⟹  `ofReal (1/K) ≤ M`.
  have hcancel : ENNReal.ofReal (1 / K) * ENNReal.ofReal K = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ (ne_of_gt hKpos),
      ENNReal.ofReal_one]
  have hmul : ENNReal.ofReal (1 / K) * 1
      ≤ ENNReal.ofReal (1 / K) * (M * ENNReal.ofReal K) := by gcongr
  have hrw : ENNReal.ofReal (1 / K) * (M * ENNReal.ofReal K) = M := by
    rw [show M * ENNReal.ofReal K = ENNReal.ofReal K * M from mul_comm _ _,
      ← mul_assoc, hcancel, one_mul]
  rwa [mul_one, hrw] at hmul

end NoWanderingDomains
