/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.GeometricToAnalytic.GeometricDifferentiable.Reciprocity
import NoWanderingDomains.Analysis.Helpers.WeightedLengthLSC

/-!
# The level-slice separating-arc bound

The bridge from σ-admissibility along curves to a Hausdorff-measure lower bound along
level sets: for a global Lipschitz potential `U` vanishing on the image left side and
`≥ α` on the image right side of the image quadrilateral `Ω = f(R)`, almost every level
`c ∈ (0, α)` satisfies

  `1 ≤ ∫_{U⁻¹(c) ∩ Ω} σ dμH¹`

whenever `σ` is admissible for the image separating (swap) family. The chain of custody:

1. **Level continuum** — conjugating by `f` and the affine chart, the rescaled potential
   `min(U ∘ f-chart, α)/α` is a continuous left-right transition function on the source
   rectangle, so `exists_preconnected_level_crossing`
   (`GeometricDifferentiable/PlaneSeparation.lean`) yields a preconnected level subset of
   the source rectangle touching bottom and top; its closure pushes forward to a compact
   connected subset `Γ_c ⊆ U⁻¹(c) ∩ Ω` joining `f(bottom)` to `f(top)`.
2. **Finite length a.e.** — `coarea_set_sharp` (`Analysis/Sobolev/Coarea/Assembly.lean`)
   bounds `∫ μH¹(U⁻¹(c) ∩ Ω) dc` by the Lipschitz constant times `vol Ω`, so
   `μH¹(U⁻¹(c) ∩ Ω) < ∞` for a.e. `c` (measurability of the slice function by
   `measurable_slice_hausdorff_one`).
3. **Simple arc** — the Eilenberg–Harrold theorem `rectifiable_continuum_simple_arc`
   (`GeometricDifferentiable/Reciprocity.lean`) extracts from `Γ_c` a simple Lipschitz arc
   `δ` joining a point of `f(bottom)` to a point of `f(top)` inside `Γ_c` (endpoints are
   distinct by injectivity of `f`, the source edges being disjoint).
4. **Membership + admissibility** — `δ` is continuous, absolutely continuous
   (`lipschitzOnWith_uIcc_absolutelyContinuousOnInterval`), starts on `f(swap-left)`, ends
   on `f(swap-right)`, and stays in `f(R)` (the swap image is the same rectangle), so it is
   a member of the image separating family and `1 ≤ ∫_δ σ ds`.
5. **Bridge to `μH¹`** — `arcLengthLineIntegral_le_setLIntegral_hausdorff`
   (`GeometricDifferentiable/Reciprocity.lean`) bounds `∫_δ σ ds` by the `μH¹`-integral of
   `σ` over the trace of `δ`, which is contained in `U⁻¹(c) ∩ Ω`.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NoWanderingDomains

/-- **The level-slice separating-arc bound.** Let `f` be a homeomorphism of `ℂ`,
`Q = axisRectQuadrilateral a b s t` and `σ` admissible for the image separating (swap)
family. If `U : ℂ → ℝ` is (globally) Lipschitz, vanishes on the image left side
`f '' Q.leftSide`, and is `≥ α > 0` on the image right side `f '' Q.rightSide`, then for
almost every level `c ∈ (0, α)`,

  `1 ≤ ∫_{U⁻¹(c) ∩ f '' Q.image} σ dμH¹`. -/
theorem level_slice_sigma_ge {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) {σ : ℂ → ℝ≥0∞}
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f))
    {U : ℂ → ℝ} {K : ℝ≥0} (hU : LipschitzWith K U)
    (hU0 : ∀ w ∈ f '' (axisRectQuadrilateral a b s t hab hst).leftSide, U w = 0)
    {α : ℝ} (hα : 0 < α)
    (hUF : ∀ w ∈ f '' (axisRectQuadrilateral a b s t hab hst).rightSide, α ≤ U w) :
    ∀ᵐ c : ℝ, c ∈ Set.Ioo 0 α →
      1 ≤ ∫⁻ z in U ⁻¹' {c} ∩ f '' (axisRectQuadrilateral a b s t hab hst).image, σ z
            ∂(μH[1] : Measure ℂ) := by
  classical
  obtain ⟨hσmeas, hσadm⟩ := hσ
  -- ### Step 0: compactness of the image region and the coarea selection of good levels.
  have hQcpt : IsCompact (axisRectQuadrilateral a b s t hab hst).image :=
    (isCompact_Icc.prod isCompact_Icc).image
      (axisRectQuadrilateral a b s t hab hst).continuous_toFun
  have hΩcpt : IsCompact (f '' (axisRectQuadrilateral a b s t hab hst).image) :=
    hQcpt.image hf.continuous
  have hΩmeas : MeasurableSet (f '' (axisRectQuadrilateral a b s t hab hst).image) :=
    hΩcpt.isClosed.measurableSet
  -- Pointwise gradient bound for the `K`-Lipschitz potential.
  have hgrad : ∀ z : ℂ, (‖fderiv ℝ U z‖₊ : ℝ≥0∞) ≤ (K : ℝ≥0∞) := by
    intro z
    have h2 : ‖fderiv ℝ U z‖₊ ≤ K := by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact norm_fderiv_le_of_lipschitz ℝ hU
    exact ENNReal.coe_le_coe.mpr h2
  -- The total level-length integral is finite (`coarea_set_sharp` + `‖∇U‖ ≤ K` + compactness).
  have htotal :
      (∫⁻ c : ℝ, μH[1] (U ⁻¹' {c} ∩ f '' (axisRectQuadrilateral a b s t hab hst).image))
        ≠ ∞ := by
    have hcoarea := Coarea.coarea_set_sharp hU hΩmeas
    have hbound :
        (∫⁻ z in f '' (axisRectQuadrilateral a b s t hab hst).image,
            (‖fderiv ℝ U z‖₊ : ℝ≥0∞) ∂volume)
          ≤ (K : ℝ≥0∞) * volume (f '' (axisRectQuadrilateral a b s t hab hst).image) := by
      calc (∫⁻ z in f '' (axisRectQuadrilateral a b s t hab hst).image,
              (‖fderiv ℝ U z‖₊ : ℝ≥0∞) ∂volume)
          ≤ ∫⁻ _ in f '' (axisRectQuadrilateral a b s t hab hst).image,
              (K : ℝ≥0∞) ∂volume := lintegral_mono fun z => hgrad z
        _ = (K : ℝ≥0∞) * volume (f '' (axisRectQuadrilateral a b s t hab hst).image) :=
          setLIntegral_const _ _
    exact ((hcoarea.trans hbound).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top hΩcpt.measure_lt_top)).ne
  -- Almost every level slice has finite `μH¹`-length.
  have hae : ∀ᵐ c : ℝ,
      μH[1] (U ⁻¹' {c} ∩ f '' (axisRectQuadrilateral a b s t hab hst).image) < ∞ :=
    ae_lt_top (Coarea.measurable_slice_hausdorff_one hU.continuous hΩcpt) htotal
  -- ### Level-independent preliminaries: the rescaled transition potential on the rectangle.
  have hvcont : Continuous fun z : ℂ => min (U (f z)) α / α :=
    ((hU.continuous.comp hf.continuous).min continuous_const).div_const α
  have hv0 : ∀ z : ℂ, z.re = a → s ≤ z.im → z.im ≤ t → min (U (f z)) α / α = 0 := by
    intro z hre him1 him2
    have hzL : z ∈ (axisRectQuadrilateral a b s t hab hst).leftSide := by
      rw [axisRectQuadrilateral_leftSide hab hst]
      exact ⟨hre, him1, him2⟩
    rw [hU0 (f z) (Set.mem_image_of_mem f hzL), min_eq_left hα.le, zero_div]
  have hv1 : ∀ z : ℂ, z.re = b → s ≤ z.im → z.im ≤ t → min (U (f z)) α / α = 1 := by
    intro z hre him1 him2
    have hzR : z ∈ (axisRectQuadrilateral a b s t hab hst).rightSide := by
      rw [axisRectQuadrilateral_rightSide hab hst]
      exact ⟨hre, him1, him2⟩
    rw [min_eq_right (hUF (f z) (Set.mem_image_of_mem f hzR)), div_self hα.ne']
  -- The coordinate rectangle is compact (it is the image of the compact unit square).
  have hrect_cpt : IsCompact {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ (s ≤ z.im ∧ z.im ≤ t)} := by
    rw [← axisRectQuadrilateral_image hab hst]
    exact hQcpt
  -- ### The a.e. selection: fix a good level `c ∈ (0, α)` with a finite-length slice.
  filter_upwards [hae] with c hfin hc
  -- ### Step 1: the preconnected level continuum in the source rectangle.
  have hc' : c / α ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨div_pos hc.1 hα, (div_lt_one hα).mpr hc.2⟩
  obtain ⟨S, hSpre, hSsub, hSlevel, ⟨p, hpS, hpim⟩, ⟨q, hqS, hqim⟩⟩ :=
    exists_preconnected_level_crossing hab.le hst.le hvcont hv0 hv1 hc'
  -- On `S` the potential takes exactly the value `c` (since `c < α`).
  have hUc : ∀ z ∈ S, U (f z) = c := by
    intro z hz
    have h' : min (U (f z)) α / α = c / α := hSlevel z hz
    have hmin : min (U (f z)) α = c := by
      have hmul := congrArg (fun x : ℝ => x * α) h'
      simpa [div_mul_cancel₀, hα.ne'] using hmul
    rcases min_eq_iff.mp hmin with h | h
    · exact h.1
    · exact absurd h.1.symm hc.2.ne
  -- ### Step 2: push the closed level continuum forward through `f`.
  have hLclosed : IsClosed {z : ℂ | U (f z) = c} :=
    isClosed_eq (hU.continuous.comp hf.continuous) continuous_const
  have hSsub' : S ⊆ {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ (s ≤ z.im ∧ z.im ≤ t)}
      ∩ {z : ℂ | U (f z) = c} :=
    fun z hz => ⟨hSsub hz, hUc z hz⟩
  have hclS : closure S ⊆ {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ (s ≤ z.im ∧ z.im ≤ t)}
      ∩ {z : ℂ | U (f z) = c} :=
    closure_minimal hSsub' (hrect_cpt.isClosed.inter hLclosed)
  have hclS_cpt : IsCompact (closure S) :=
    hrect_cpt.of_isClosed_subset isClosed_closure (hclS.trans Set.inter_subset_left)
  have hΓcpt : IsCompact (f '' closure S) := hclS_cpt.image hf.continuous
  have hclconn : IsConnected (closure S) := ⟨⟨p, subset_closure hpS⟩, hSpre.closure⟩
  have hΓconn : IsConnected (f '' closure S) := hclconn.image f hf.continuous.continuousOn
  have hΓsub : f '' closure S
      ⊆ U ⁻¹' {c} ∩ f '' (axisRectQuadrilateral a b s t hab hst).image := by
    rintro w ⟨z, hz, rfl⟩
    refine ⟨(hclS hz).2, ?_⟩
    have hzrect := (hclS hz).1
    rw [← axisRectQuadrilateral_image hab hst] at hzrect
    exact Set.mem_image_of_mem f hzrect
  have hΓfin : μH[1] (f '' closure S) ≠ ∞ := ((measure_mono hΓsub).trans_lt hfin).ne
  -- Endpoints on the bottom and top edges are distinct, and so are their `f`-images.
  have hpq : p ≠ q := by
    intro h
    rw [h, hqim] at hpim
    exact hst.ne' hpim
  have hPQ : f p ≠ f q := fun h => hpq (hf.injective h)
  have hPmem : f p ∈ f '' closure S := Set.mem_image_of_mem f (subset_closure hpS)
  have hQmem : f q ∈ f '' closure S := Set.mem_image_of_mem f (subset_closure hqS)
  -- ### Step 3: extract the Eilenberg–Harrold simple Lipschitz arc inside the continuum.
  obtain ⟨δ, hδ0, hδ1, hδcont, ⟨Kδ, hδlip⟩, hδinj, hδmem⟩ :=
    rectifiable_continuum_simple_arc hΓcpt hΓconn hΓfin hPmem hQmem hPQ
  -- ### Step 4: the arc is a member of the image separating (swap) family.
  have hδac : AbsolutelyContinuousOnInterval δ 0 1 :=
    lipschitzOnWith_uIcc_absolutelyContinuousOnInterval hδlip
  have hδfam : δ ∈ (axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f := by
    refine ⟨hδcont, hδac, ?_, ?_, ?_⟩
    · -- `δ 0 = f p` lies on the image of the swap left side (the bottom edge).
      rw [hδ0, axisRectQuadrilateralSwap_leftSide hab hst]
      exact Set.mem_image_of_mem f ⟨hpim, (hSsub hpS).1⟩
    · -- `δ 1 = f q` lies on the image of the swap right side (the top edge).
      rw [hδ1, axisRectQuadrilateralSwap_rightSide hab hst]
      exact Set.mem_image_of_mem f ⟨hqim, (hSsub hqS).1⟩
    · -- The trace stays in the image of the (common) rectangle.
      intro τ hτ
      rw [axisRectQuadrilateralSwap_image hab hst]
      exact (hΓsub (hδmem τ hτ)).2
  have hlen : 1 ≤ arcLengthLineIntegral σ δ := hσadm δ hδfam
  -- ### Step 5: bridge the arc-length integral to the Hausdorff integral over the slice.
  have hbridge := arcLengthLineIntegral_le_setLIntegral_hausdorff hσmeas hδcont hδac hδinj
  have htrace : δ '' Set.Icc (0 : ℝ) 1
      ⊆ U ⁻¹' {c} ∩ f '' (axisRectQuadrilateral a b s t hab hst).image := by
    rintro w ⟨τ, hτ, rfl⟩
    exact hΓsub (hδmem τ hτ)
  exact hlen.trans (hbridge.trans (lintegral_mono_set htrace))

end NoWanderingDomains
