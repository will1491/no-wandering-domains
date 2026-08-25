/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.GeometricToAnalytic.Loewner.ClaimTwo
import NoWanderingDomains.QC.GeometricToAnalytic.Loewner.LevelSlice
import NoWanderingDomains.QC.GeometricToAnalytic.Loewner.CoareaSlice

/-!
# Loewner planar reciprocity — the image cross-bound

The planar Loewner / Beurling reciprocity inequality consumed by
`imageConjugate_cross_bound` (`GeometricDifferentiable/ReciprocityAssembly.lean`) on the
geometric ⇒ analytic critical path: for a homeomorphism `f` and finite-energy densities
`ρ`, `σ` admissible for the image crossing family and the image separating (swap) family of
an axis rectangle, the cross-product integrates to at least `1`,

  `1 ≤ ∫⁻ z, ρ z · σ z`.

This is the headline reciprocity inequality. Through `imageConjugate_cross_bound` it feeds
`conjugateImageModulus_reciprocity` (`1 ≤ M(Γ) · M(Γ*)`), then
`square_imageCurveFamily_modulus_ge` (`M(image square) ≥ 1/K`), the modulus blow-up
`squareQuad_imageModulus_ge`, and ultimately the infinitesimal dilatation bound
`IsQCGeometric.infinitesimal_dilatation`.

The statement is purely topological — no quasiconformality of `f` enters; `K` enters the
chain exactly once, downstream, at `square_imageCurveFamily_modulus_ge`. The finite-energy
hypotheses on both densities are the honest classical form: the closest literature statement
(Eriksson-Bique–Poggi-Corradini, *On the sharp lower bound for duality of modulus*, Proc.
AMS 150 (2022), Theorem 1.1) carries the dual-exponent integrability `σ ∈ L^q` in exactly
this role, and the downstream modulus reciprocity consumes the bound only through
finite-energy densities (the Rengel witnesses guard both infima). Densities transported
through a non-conformal homeomorphism lose admissibility (Brakalova–Markina–Vasil'ev,
*Extremal functions for modules of systems of measures*, Example 4), so the argument runs
intrinsically on the image plane — no change of variables through `f` is used anywhere.

## Proof route (Eriksson-Bique–Poggi-Corradini, transplanted to the plane)

Write `Ω = f(R)`, `E = f(left side)`, `F = f(right side)` — a compact preconnected set with
two disjoint closed boundary continua. Fix a cushion scale `n` and a Vitali–Carathéodory
envelope `Φ ≥ max(ρ, 1/n)` — lower semicontinuous, with squared energy on `Ω` within `1/n`
of that of `max(ρ, 1/n)` (`exists_lsc_sq_approx`, `Loewner/CoareaSlice.lean`). Its
Moreau–Yosida envelopes `g_i` (`Analysis/Helpers/MoreauYosida.lean`) are continuous, `i`-Lipschitz,
increasing, and recover `Φ` pointwise.

1. **Chain potential** (`Loewner/ChainPotential.lean`): the discrete Beurling potential
   `u_i = chainPotential D_i E g_i (1/(i+1))` over chains through the closed thickening
   `D_i ⊇ Ω`; `u_i` vanishes on `E`, is `max(i, i+1)`-Lipschitz on `D_i`, and extends to a
   global Lipschitz `U_i` (`LipschitzOnWith.extend_real`, McShane).
2. **Boundary values** (`Loewner/ClaimTwo.lean`, the Eriksson-Bique–Poggi-Corradini
   compactness argument): admissibility of `ρ` against the crossing family forces
   `u_i ≥ 1 − δ` on `F` for `i` large — a cheap chain would interpolate to a Lipschitz
   curve, converge (Arzelà–Ascoli, cushion-bounded length) to a crossing curve in `Ω` of
   `Φ`-length `< 1`, contradicting `ρ ≤ Φ` and admissibility.
3. **Eikonal**: `‖fderiv U_i‖ ≤ g_i` at every differentiability point of the interior of
   `D_i ⊇ Ω` (`norm_fderiv_le_of_local_bound` — pointwise, by continuity of `g_i`), hence
   a.e. on `Ω` by Rademacher.
4. **Level slices** (`Loewner/LevelSlice.lean`): for a.e. `c ∈ (0, 1−δ)` the level set
   `U_i⁻¹(c) ∩ Ω` carries `∫ σ dμH¹ ≥ 1` — the plane-separation level continuum
   (`exists_preconnected_level_crossing`), the Eilenberg–Harrold simple arc, membership in
   the separating family, and the Hausdorff arc-length bridge.
5. **Co-area** (`Loewner/CoareaSlice.lean`, on the sharp Euclidean engine
   `eilenberg_coarea_grad_le`): `ofReal (1−δ) ≤ ∫_Ω σ · g_i ≤ ∫_Ω σ · Φ`.
6. **Endgame**: `∫_Ω σΦ ≤ ∫ σρ + ‖σ‖₂ · (‖Φ − max(ρ,1/n)‖₂ + ‖max(ρ,1/n) − ρ‖₂)` by
   Cauchy–Schwarz; both error norms vanish as `n → ∞` (Vitali–Carathéodory closeness and
   the cushion), giving `1 ≤ ∫ ρσ`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NoWanderingDomains

/-- **Loewner image cross-bound — the planar reciprocity inequality.**

For a homeomorphism `f : ℂ → ℂ` and admissible finite-energy densities
`ρ, σ : ℂ → ℝ≥0∞` for the image crossing family and the image separating (swap) family of
an axis rectangle, the cross-product integrates to at least `1`:

  `1 ≤ ∫⁻ z, ρ z * σ z`.

This discharges `imageConjugate_cross_bound`
(`GeometricDifferentiable/ReciprocityAssembly.lean`) by a one-line call. The statement is
purely topological — no quasiconformality of `f` is assumed; the finite-energy hypotheses
are the honest classical form (see the file docstring). The proof is the
Eriksson-Bique–Poggi-Corradini chain-potential argument on the image plane; see the file
docstring for the step-by-step route. -/
theorem loewner_image_cross_bound_axisRect {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t)
    {ρ σ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f))
    (hρE : (∫⁻ z, (ρ z) ^ 2) ≠ ⊤) (hσE : (∫⁻ z, (σ z) ^ 2) ≠ ⊤) :
    1 ≤ ∫⁻ z, ρ z * σ z := by
  classical
  -- ### Setup: the image domain `Ω` and its two boundary continua `E`, `F`
  set Q : Quadrilateral := axisRectQuadrilateral a b s t hab hst with hQdef
  set Ω : Set ℂ := f '' Q.image with hΩdef
  set E : Set ℂ := f '' Q.leftSide with hEdef
  set F : Set ℂ := f '' Q.rightSide with hFdef
  have hΩcpt : IsCompact Ω :=
    ((isCompact_Icc.prod isCompact_Icc).image Q.continuous_toFun).image hf.continuous
  have hΩconn : IsPreconnected Ω :=
    ((((convex_Icc (0:ℝ) 1).prod (convex_Icc (0:ℝ) 1)).isPreconnected).image _
      Q.continuous_toFun.continuousOn).image _ hf.continuous.continuousOn
  have hEcpt : IsCompact E :=
    ((isCompact_singleton.prod isCompact_Icc).image Q.continuous_toFun).image hf.continuous
  have hFcpt : IsCompact F :=
    ((isCompact_singleton.prod isCompact_Icc).image Q.continuous_toFun).image hf.continuous
  have hEΩ : E ⊆ Ω := by
    have hsub : Q.leftSide ⊆ Q.image :=
      Set.image_mono (Set.prod_mono
        (Set.singleton_subset_iff.mpr (Set.left_mem_Icc.mpr zero_le_one)) subset_rfl)
    exact Set.image_mono hsub
  have hFΩ : F ⊆ Ω := by
    have hsub : Q.rightSide ⊆ Q.image :=
      Set.image_mono (Set.prod_mono
        (Set.singleton_subset_iff.mpr (Set.right_mem_Icc.mpr zero_le_one)) subset_rfl)
    exact Set.image_mono hsub
  have hEne : E.Nonempty :=
    ((image_axisRectQuadrilateral_sides_disjoint hf hab hst).2).image f
  have hΩmeas : MeasurableSet Ω := hΩcpt.isClosed.measurableSet
  have hvolΩ : volume Ω ≠ ⊤ := hΩcpt.measure_lt_top.ne
  -- admissibility of `ρ`, repackaged for the crossing curves of the image quadrilateral
  have hadm : ∀ γ : ℝ → ℂ, Continuous γ → AbsolutelyContinuousOnInterval γ 0 1 →
      γ 0 ∈ E → γ 1 ∈ F → (∀ t' ∈ Set.Icc (0 : ℝ) 1, γ t' ∈ Ω) →
      1 ≤ arcLengthLineIntegral ρ γ :=
    fun γ hγc hγac hγ0 hγ1 hγtr => hρ.2 γ ⟨hγc, hγac, hγ0, hγ1, hγtr⟩
  -- ### The quantitative cross-bound at cushion scale `n`
  have key : ∀ n : ℕ, 2 ≤ n →
      ENNReal.ofReal (1 - 1/(n:ℝ)) ≤ (∫⁻ z, ρ z * σ z) +
        ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (((n:ℝ≥0∞))⁻¹) ^ (1/2:ℝ) +
          ((n:ℝ≥0∞))⁻¹ * ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (volume Ω) ^ (1/2:ℝ))) := by
    intro n hn
    -- numerology of the cushion
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) < n := by linarith
    have hnne : ((n:ℝ≥0∞)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hinv0 : ((n:ℝ≥0∞))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)
    have hinvtop : ((n:ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hnne
    have hofr : ENNReal.ofReal (1/(n:ℝ)) = ((n:ℝ≥0∞))⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos hn0, ENNReal.ofReal_natCast]
    have hδpos : (0:ℝ) < 1/(n:ℝ) := div_pos one_pos hn0
    have hα : (0:ℝ) < 1 - 1/(n:ℝ) := by
      have h1 : 1/(n:ℝ) < 1 := by
        rw [div_lt_one hn0]; linarith
      linarith
    -- Step 1: Vitali–Carathéodory square-envelope `Φ ≥ max (ρ, 1/n)`
    obtain ⟨Φ, hΦlsc, hΦge, hΦE⟩ :=
      exists_lsc_sq_approx hρ.1 hΩmeas hvolΩ (ε := ((n:ℝ≥0∞))⁻¹) hinv0 hinv0 hinvtop
    have hΦρ : ∀ z, ρ z ≤ Φ z := fun z => (le_max_left _ _).trans (hΦge z)
    have hΦε : ∀ z, ENNReal.ofReal (1/(n:ℝ)) ≤ Φ z := fun z => by
      rw [hofr]; exact (le_max_right _ _).trans (hΦge z)
    have hΦmeas : Measurable Φ := hΦlsc.measurable
    have hmmeas : Measurable fun z => max (ρ z) ((n:ℝ≥0∞))⁻¹ := hρ.1.max measurable_const
    -- Step 2: ClaimTwo — the chain potential is `≥ 1 − 1/n` on `F` for one large scale `i₀`
    obtain ⟨i₀, hi₀⟩ := chainPotential_limit_one hΩcpt hΩconn hEcpt.isClosed hFcpt.isClosed
      hEΩ hFΩ hEne hadm hΦlsc hΦρ hδpos hΦε hδpos
    -- Step 3: the chain potential at scale `i₀` and its McShane extension
    set h : ℝ := 1 / (i₀ + 1 : ℝ) with hhdef
    have hh : 0 < h := by rw [hhdef]; positivity
    set D : Set ℂ := closure (Metric.thickening h Ω) with hDdef
    set g : ℂ → ℝ := moreauEnvelope Φ i₀ with hgdef
    have hg0 : ∀ y, 0 ≤ g y := moreauEnvelope_nonneg Φ i₀
    have hΩD : Ω ⊆ D := (Metric.self_subset_thickening hh Ω).trans subset_closure
    have hDconn : IsPreconnected D := isPreconnected_closure_thickening hΩconn hh
    have hED : (E ∩ D).Nonempty := by
      obtain ⟨e, he⟩ := hEne
      exact ⟨e, he, hΩD (hEΩ he)⟩
    have hne : ∀ w ∈ D, (chainCosts D E g h w).Nonempty := fun w hw =>
      chainCosts_nonempty hDconn hh hED hw
    have hgM : ∀ y ∈ D, g y ≤ ((i₀ : ℝ≥0) : ℝ) := by
      intro y _
      refine (moreauEnvelope_le Φ i₀ y).trans ?_
      have h2 : (min (Φ y) ((i₀:ℝ≥0∞))).toReal ≤ ((i₀:ℝ≥0∞)).toReal :=
        ENNReal.toReal_mono (ENNReal.natCast_ne_top _) (min_le_right _ _)
      simpa [ENNReal.toReal_natCast] using h2
    have hulip := chainPotential_lipschitzOnWith hh hg0 hgM hne
    obtain ⟨U, hUlip, hUeq⟩ := hulip.extend_real
    -- boundary values of the extension
    have hU0 : ∀ w ∈ E, U w = 0 := fun w hw => by
      rw [← hUeq (hΩD (hEΩ hw))]
      exact chainPotential_eq_zero hg0 h ⟨hw, hΩD (hEΩ hw)⟩
    have hUF : ∀ w ∈ F, 1 - 1/(n:ℝ) ≤ U w := fun w hw => by
      rw [← hUeq (hΩD (hFΩ hw))]
      exact hi₀ i₀ le_rfl w hw
    -- Step 4: level slices carry `∫ σ dμH¹ ≥ 1` for a.e. level
    have hslice := level_slice_sigma_ge hf hab hst hσ hUlip hU0 hα hUF
    -- Step 5: the eikonal inequality `‖fderiv U‖ ≤ g` a.e. on `Ω`
    have hO : IsOpen (Metric.thickening h Ω) := Metric.isOpen_thickening
    have hOD : Metric.thickening h Ω ⊆ D := subset_closure
    have hgcont : ContinuousOn g (Metric.thickening h Ω) :=
      (moreauEnvelope_lipschitz Φ i₀).continuous.continuousOn
    have hloc : ∀ x ∈ Metric.thickening h Ω, ∀ y ∈ Metric.thickening h Ω,
        dist x y ≤ h → |U x - U y| ≤ max (g x) (g y) * dist x y := by
      intro x hx y hy hxy
      rw [← hUeq (hOD hx), ← hUeq (hOD hy)]
      exact chainPotential_local_bound hh hg0 hne (hOD hx) (hOD hy) hxy
    have heik : ∀ᵐ z, z ∈ Ω → (‖fderiv ℝ U z‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (g z) := by
      filter_upwards [hUlip.ae_differentiableAt] with z hz hzΩ
      have hb := norm_fderiv_le_of_local_bound hO hgcont hh hloc
        (Metric.self_subset_thickening hh Ω hzΩ) hz
      exact le_trans (ofReal_norm _).symm.le (ENNReal.ofReal_le_ofReal hb)
    have hGm : Measurable fun z => ENNReal.ofReal (g z) :=
      (moreauEnvelope_lipschitz Φ i₀).continuous.measurable.ennreal_ofReal
    -- Step 6: co-area
    have hcoarea := coarea_slice_assembly hUlip hσ.1 hΩmeas hGm heik hα hslice
    -- Step 7: `g ≤ Φ` under the integral
    have h9 : (∫⁻ z in Ω, σ z * ENNReal.ofReal (g z)) ≤ ∫⁻ z in Ω, σ z * Φ z := by
      refine lintegral_mono fun z => ?_
      exact mul_le_mul' le_rfl ((ofReal_moreauEnvelope_le Φ i₀ z).trans (min_le_left _ _))
    -- Step 8: split `σ·Φ ≤ σ·(Φ − max) + σ·ρ + σ·n⁻¹` and integrate
    have h10 : (∫⁻ z in Ω, σ z * Φ z) ≤
        (∫⁻ z in Ω, σ z * (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹)) +
          ((∫⁻ z in Ω, σ z * ρ z) + (∫⁻ z in Ω, σ z * ((n:ℝ≥0∞))⁻¹)) := by
      have hpt : ∀ z, σ z * Φ z ≤
          σ z * (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) + (σ z * ρ z + σ z * ((n:ℝ≥0∞))⁻¹) := by
        intro z
        have hsplit : Φ z ≤ (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) + (ρ z + ((n:ℝ≥0∞))⁻¹) :=
          calc Φ z = (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) + max (ρ z) ((n:ℝ≥0∞))⁻¹ :=
                (tsub_add_cancel_of_le (hΦge z)).symm
            _ ≤ (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) + (ρ z + ((n:ℝ≥0∞))⁻¹) :=
                add_le_add_right (max_le_add_of_nonneg (zero_le) (zero_le)) _
        calc σ z * Φ z
            ≤ σ z * ((Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) + (ρ z + ((n:ℝ≥0∞))⁻¹)) :=
              mul_le_mul' le_rfl hsplit
          _ = σ z * (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) + (σ z * ρ z + σ z * ((n:ℝ≥0∞))⁻¹) := by
              ring
      calc (∫⁻ z in Ω, σ z * Φ z)
          ≤ ∫⁻ z in Ω, (σ z * (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) +
              (σ z * ρ z + σ z * ((n:ℝ≥0∞))⁻¹)) := lintegral_mono hpt
        _ = (∫⁻ z in Ω, σ z * (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹)) +
              ∫⁻ z in Ω, (σ z * ρ z + σ z * ((n:ℝ≥0∞))⁻¹) :=
            lintegral_add_left (hσ.1.mul (hΦmeas.sub hmmeas)) _
        _ = (∫⁻ z in Ω, σ z * (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹)) +
              ((∫⁻ z in Ω, σ z * ρ z) + (∫⁻ z in Ω, σ z * ((n:ℝ≥0∞))⁻¹)) := by
            rw [lintegral_add_left (hσ.1.fun_mul hρ.1)]
    -- Step 9: Cauchy–Schwarz on the error term
    have hsub_sq : ∀ z, (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2 ≤
        (Φ z) ^ 2 - (max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2 := by
      intro z
      rcases eq_or_ne (max (ρ z) ((n:ℝ≥0∞))⁻¹) ⊤ with hm | hm
      · rw [hm, ENNReal.sub_top, zero_pow (by norm_num)]
        exact zero_le
      · refine (ENNReal.cancel_of_ne (ENNReal.pow_ne_top hm)).le_tsub_of_add_le_right ?_
        calc (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2 + (max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2
            ≤ ((Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2 +
                2 * (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) * max (ρ z) ((n:ℝ≥0∞))⁻¹) +
                (max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2 :=
              add_le_add_left le_self_add _
          _ = ((Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) + max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2 :=
              (add_sq _ _).symm
          _ = (Φ z) ^ 2 := by rw [tsub_add_cancel_of_le (hΦge z)]
    have hm_sq_le : ∀ z,
        (max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2 ≤ (ρ z) ^ 2 + (((n:ℝ≥0∞))⁻¹) ^ 2 := by
      intro z
      rcases le_total (ρ z) (((n:ℝ≥0∞))⁻¹) with hc | hc
      · rw [max_eq_right hc]; exact le_add_self
      · rw [max_eq_left hc]; exact le_self_add
    have hmint : (∫⁻ z in Ω, (max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono hm_sq_le)
      rw [lintegral_add_right _ measurable_const, lintegral_const,
        Measure.restrict_apply_univ]
      exact ENNReal.add_ne_top.mpr
        ⟨ne_top_of_le_ne_top hρE (setLIntegral_le_lintegral _ _),
         ENNReal.mul_ne_top (ENNReal.pow_ne_top hinvtop) hvolΩ⟩
    have hint_sub : (∫⁻ z in Ω, (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2) ≤ ((n:ℝ≥0∞))⁻¹ :=
      calc (∫⁻ z in Ω, (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2)
          ≤ ∫⁻ z in Ω, ((Φ z) ^ 2 - (max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2) :=
            lintegral_mono hsub_sq
        _ = (∫⁻ z in Ω, (Φ z) ^ 2) - ∫⁻ z in Ω, (max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2 :=
            lintegral_sub (hmmeas.pow_const 2) hmint
              (Filter.Eventually.of_forall fun z => pow_le_pow_left' (hΦge z) 2)
        _ ≤ ((∫⁻ z in Ω, (max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2) + ((n:ℝ≥0∞))⁻¹) -
              ∫⁻ z in Ω, (max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2 := tsub_le_tsub_right hΦE _
        _ = ((n:ℝ≥0∞))⁻¹ := ENNReal.add_sub_cancel_left hmint
    have hCS_A : (∫⁻ z in Ω, σ z * (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹)) ≤
        (∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (((n:ℝ≥0∞))⁻¹) ^ (1/2:ℝ) := by
      have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict Ω)
        Real.HolderConjugate.two_two (f := σ)
        (g := fun z => Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹)
        hσ.1.aemeasurable ((hΦmeas.sub hmmeas).aemeasurable)
      have hmul : (fun z => (σ * fun z' => Φ z' - max (ρ z') ((n:ℝ≥0∞))⁻¹) z) =
          fun z => σ z * (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) := rfl
      have hA : (∫⁻ z in Ω, σ z ^ (2:ℝ)) = ∫⁻ z in Ω, σ z ^ 2 :=
        lintegral_congr fun z => ENNReal.rpow_two _
      have hB : (∫⁻ z in Ω, (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ (2:ℝ)) =
          ∫⁻ z in Ω, (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹) ^ 2 :=
        lintegral_congr fun z => ENNReal.rpow_two _
      rw [hmul, hA, hB] at hCS
      exact hCS.trans (mul_le_mul' le_rfl
        (ENNReal.rpow_le_rpow hint_sub (by norm_num)))
    -- Step 10: the cushion term
    have hC : (∫⁻ z in Ω, σ z * ((n:ℝ≥0∞))⁻¹) ≤
        ((n:ℝ≥0∞))⁻¹ * ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (volume Ω) ^ (1/2:ℝ)) := by
      have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict Ω)
        Real.HolderConjugate.two_two (f := σ) (g := fun _ => 1)
        hσ.1.aemeasurable aemeasurable_const
      simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow] at hCS
      rw [lintegral_one, Measure.restrict_apply_univ] at hCS
      have hA : (∫⁻ z in Ω, σ z ^ (2:ℝ)) = ∫⁻ z in Ω, σ z ^ 2 :=
        lintegral_congr fun z => ENNReal.rpow_two _
      rw [hA] at hCS
      calc (∫⁻ z in Ω, σ z * ((n:ℝ≥0∞))⁻¹)
          = (∫⁻ z in Ω, σ z) * ((n:ℝ≥0∞))⁻¹ := lintegral_mul_const _ hσ.1
        _ ≤ ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (volume Ω) ^ (1/2:ℝ)) * ((n:ℝ≥0∞))⁻¹ :=
            mul_le_mul' hCS le_rfl
        _ = ((n:ℝ≥0∞))⁻¹ * ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (volume Ω) ^ (1/2:ℝ)) :=
            mul_comm _ _
    -- Step 11: the main term
    have hB' : (∫⁻ z in Ω, σ z * ρ z) ≤ ∫⁻ z, ρ z * σ z :=
      calc (∫⁻ z in Ω, σ z * ρ z) = ∫⁻ z in Ω, ρ z * σ z :=
            lintegral_congr fun z => mul_comm _ _
        _ ≤ ∫⁻ z, ρ z * σ z := setLIntegral_le_lintegral _ _
    -- assemble
    calc ENNReal.ofReal (1 - 1/(n:ℝ))
        ≤ ∫⁻ z in Ω, σ z * ENNReal.ofReal (g z) := hcoarea
      _ ≤ ∫⁻ z in Ω, σ z * Φ z := h9
      _ ≤ (∫⁻ z in Ω, σ z * (Φ z - max (ρ z) ((n:ℝ≥0∞))⁻¹)) +
            ((∫⁻ z in Ω, σ z * ρ z) + (∫⁻ z in Ω, σ z * ((n:ℝ≥0∞))⁻¹)) := h10
      _ ≤ ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (((n:ℝ≥0∞))⁻¹) ^ (1/2:ℝ)) +
            ((∫⁻ z, ρ z * σ z) +
              ((n:ℝ≥0∞))⁻¹ * ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (volume Ω) ^ (1/2:ℝ))) :=
            add_le_add hCS_A (add_le_add hB' hC)
      _ = (∫⁻ z, ρ z * σ z) +
            ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (((n:ℝ≥0∞))⁻¹) ^ (1/2:ℝ) +
              ((n:ℝ≥0∞))⁻¹ * ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (volume Ω) ^ (1/2:ℝ))) := by
            ring
  -- ### Let the cushion scale `n → ∞`
  have hS : ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ne_top_of_le_ne_top hσE (setLIntegral_le_lintegral _ _))
  have h1 : Filter.Tendsto (fun k : ℕ => ((k:ℝ≥0∞))⁻¹) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero
  have h2 : Filter.Tendsto (fun k : ℕ => (((k:ℝ≥0∞))⁻¹) ^ (1/2:ℝ))
      Filter.atTop (nhds 0) := by
    have h3 := ((ENNReal.continuous_rpow_const (y := 1/2)).tendsto 0).comp h1
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)] using h3
  have herrA : Filter.Tendsto
      (fun k : ℕ => (∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (((k:ℝ≥0∞))⁻¹) ^ (1/2:ℝ))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul h2 (Or.inr hS)
  have herrC : Filter.Tendsto
      (fun k : ℕ => ((k:ℝ≥0∞))⁻¹ *
        ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (volume Ω) ^ (1/2:ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const h1
      (Or.inr (ENNReal.mul_ne_top hS (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hvolΩ)))
  have hrhs : Filter.Tendsto (fun k : ℕ => (∫⁻ z, ρ z * σ z) +
      ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (((k:ℝ≥0∞))⁻¹) ^ (1/2:ℝ) +
        ((k:ℝ≥0∞))⁻¹ * ((∫⁻ z in Ω, σ z ^ 2) ^ (1/2:ℝ) * (volume Ω) ^ (1/2:ℝ))))
      Filter.atTop (nhds (∫⁻ z, ρ z * σ z)) := by
    simpa using tendsto_const_nhds.add (herrA.add herrC)
  have hlhs : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (1 - 1/(k:ℝ)))
      Filter.atTop (nhds 1) := by
    have hr : Filter.Tendsto (fun k : ℕ => 1 - 1/(k:ℝ)) Filter.atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hr
  exact le_of_tendsto_of_tendsto hlhs hrhs (Filter.eventually_atTop.2 ⟨2, key⟩)

end NoWanderingDomains
