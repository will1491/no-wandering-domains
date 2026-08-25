/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.GeometricToAnalytic.GeometricDifferentiable.Primitives

/-!
# Geometric differentiability: plane-separation topology and the winding contradiction

The ρ-potential witness, path-reversal / AC-curve differentiability helpers, the point-set
topology of the plane-separation core (`rectLevel_*`), and the continuous-argument confinement
and square-crossing winding contradiction. Part of the reverse length-area development.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal Real

namespace NoWanderingDomains

section RhoPotentialWitness

variable {f : ℂ → ℂ} {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}

/-! #### Path-reversal helpers and a.e. differentiability of AC curves

For the two-sided cheap-connector statement we need to turn a cheap route `z ⤳ y` into a cheap
route `y ⤳ z`. The reversal `reversePath δ t = δ (1 − t)` keeps continuity, absolute continuity,
image-membership, swaps the endpoints, and — crucially — has the **same** `ρ`-arc-length
(`arcLengthLineIntegral_reversePath`), because its derivative is the negative of `δ'(1 − t)` (so
the integrand is unchanged after the measure-preserving reflection `t ↦ 1 − t` of the unit
interval). -/

/-- The **reversal** of a path `δ : ℝ → ℂ`, parametrized on `[0, 1]`: `reversePath δ t = δ (1 − t)`.
It traverses `δ` backwards, swapping the endpoints. -/
noncomputable def reversePath (δ : ℝ → ℂ) : ℝ → ℂ := fun t => δ (1 - t)

@[simp] theorem reversePath_zero (δ : ℝ → ℂ) : reversePath δ 0 = δ 1 := by simp [reversePath]
@[simp] theorem reversePath_one (δ : ℝ → ℂ) : reversePath δ 1 = δ 0 := by simp [reversePath]

/-- The reversal of a continuous path is continuous. -/
theorem reversePath_continuous {δ : ℝ → ℂ} (hδ : Continuous δ) : Continuous (reversePath δ) :=
  hδ.comp (by fun_prop)

/-- If `δ` stays in `S` on `[0, 1]`, so does its reversal `reversePath δ`. -/
theorem reversePath_mem {δ : ℝ → ℂ} {S : Set ℂ}
    (hδ : ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ S) : ∀ t ∈ Set.Icc (0 : ℝ) 1, reversePath δ t ∈ S := by
  intro t ht; rw [Set.mem_Icc] at ht
  exact hδ _ (Set.mem_Icc.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩)

/-- **Absolute continuity is preserved under path reversal.** The reflection `x ↦ 1 − x` is a
length-preserving, disjointness-preserving bijection of `[0, 1]`, so the `ε`-`δ` total-variation
criterion transfers verbatim. -/
theorem reversePath_ac {δ : ℝ → ℂ} (hδ : AbsolutelyContinuousOnInterval δ 0 1) :
    AbsolutelyContinuousOnInterval (reversePath δ) 0 1 := by
  have hmin : ∀ p q : ℝ, min (1 - p) (1 - q) = 1 - max p q := by
    intro p q; rw [max_def]; split_ifs with h
    · rw [min_eq_right (by linarith)]
    · rw [min_eq_left (by linarith)]
  have hmax : ∀ p q : ℝ, max (1 - p) (1 - q) = 1 - min p q := by
    intro p q; rw [min_def]; split_ifs with h
    · rw [max_eq_left (by linarith)]
    · rw [max_eq_right (by linarith)]
  rw [absolutelyContinuousOnInterval_iff] at hδ ⊢
  intro ε hε
  obtain ⟨D, hD, hD'⟩ := hδ ε hε
  refine ⟨D, hD, fun E hE hlen => ?_⟩
  set IL : ℕ → ℝ × ℝ := fun i => (1 - (E.2 i).1, 1 - (E.2 i).2) with hIL
  have hEmem : ((E.1, IL) : ℕ × (ℕ → ℝ × ℝ)) ∈
      AbsolutelyContinuousOnInterval.disjWithin (0:ℝ) 1 := by
    refine ⟨fun i hi => ?_, ?_⟩
    · have h := hE.1 i hi
      have hmaps : ∀ x ∈ Set.uIcc (0:ℝ) 1, (1 - x) ∈ Set.uIcc (0:ℝ) 1 := by
        intro x hx
        rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at hx
        rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc]
        exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
      exact ⟨hmaps _ h.1, hmaps _ h.2⟩
    · intro i hi j hj hij
      have hdisj := hE.2 hi hj hij
      simp only [Function.onFun, hIL, Set.uIoc, Set.disjoint_iff_inter_eq_empty] at hdisj ⊢
      rw [← Set.disjoint_iff_inter_eq_empty, Set.Ioc_disjoint_Ioc] at hdisj ⊢
      rw [hmin, hmin, hmax, hmax, hmin, hmax]
      linarith [hdisj]
  have hlenscale : ∑ i ∈ Finset.range E.1, dist (IL i).1 (IL i).2
      = ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hIL, Real.dist_eq]
    rw [show (1 - (E.2 i).1) - (1 - (E.2 i).2) = -((E.2 i).1 - (E.2 i).2) by ring, abs_neg]
  have hlen' : ∑ i ∈ Finset.range E.1, dist (IL i).1 (IL i).2 < D := by
    rw [hlenscale]; exact hlen
  have hkey := hD' (E.1, IL) hEmem hlen'
  convert hkey using 2 with i hi
  exact rfl

/-- **A.e. differentiability of an absolutely continuous `ℂ`-valued curve.** Its real and imaginary
parts are absolutely continuous (compose with the `1`-Lipschitz coordinate projections), hence
differentiable a.e. by Mathlib's `AbsolutelyContinuousOnInterval.ae_differentiableAt`; a function
`ℝ → ℂ` is `ℝ`-differentiable wherever both parts are. -/
theorem ac_complex_ae_differentiableAt {δ : ℝ → ℂ}
    (hδac : AbsolutelyContinuousOnInterval δ 0 1) :
    ∀ᵐ x, x ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ δ x := by
  have hreL : LipschitzWith 1 (fun z : ℂ => z.re) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, ← Complex.sub_re]
    rw [dist_eq_norm]; exact Complex.abs_re_le_norm _
  have himL : LipschitzWith 1 (fun z : ℂ => z.im) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, ← Complex.sub_im]
    rw [dist_eq_norm]; exact Complex.abs_im_le_norm _
  have hre : AbsolutelyContinuousOnInterval (fun t => (δ t).re) 0 1 :=
    absolutelyContinuousOnInterval_comp_lipschitzOnWith (S := Set.univ)
      hreL.lipschitzOnWith hδac (fun t _ => Set.mem_univ _)
  have him : AbsolutelyContinuousOnInterval (fun t => (δ t).im) 0 1 :=
    absolutelyContinuousOnInterval_comp_lipschitzOnWith (S := Set.univ)
      himL.lipschitzOnWith hδac (fun t _ => Set.mem_univ _)
  filter_upwards [hre.ae_differentiableAt, him.ae_differentiableAt] with x hxr hxi hmem
  have hr := hxr hmem
  have hi := hxi hmem
  have heq : δ = fun t => Complex.equivRealProdCLM.symm ((δ t).re, (δ t).im) := by
    ext t; simp [Complex.equivRealProdCLM_symm_apply]
  rw [heq]
  exact (Complex.equivRealProdCLM.symm.differentiableAt).comp x (hr.prodMk hi)

/-- **Path reversal preserves the `ρ`-arc-length.** Since `deriv (reversePath δ) t = −δ'(1 − t)`
a.e. (`δ` is differentiable a.e. by `ac_complex_ae_differentiableAt`), the integrand is unchanged in
norm, and the measure-preserving reflection `t ↦ 1 − t` of the unit interval leaves the integral
fixed. -/
theorem arcLengthLineIntegral_reversePath (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ) {δ : ℝ → ℂ}
    (hδac : AbsolutelyContinuousOnInterval δ 0 1) (hδcont : Continuous δ) :
    arcLengthLineIntegral ρ (reversePath δ) = arcLengthLineIntegral ρ δ := by
  have hδac_diff := ac_complex_ae_differentiableAt hδac
  unfold arcLengthLineIntegral
  have hmp : MeasurePreserving (fun x : ℝ => 1 - x) volume volume :=
    volume.measurePreserving_sub_left 1
  have hbad : ∀ᵐ t, (1 - t) ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ δ (1 - t) :=
    hmp.quasiMeasurePreserving.ae hδac_diff
  have hcong : ∫⁻ t in Set.Icc (0:ℝ) 1, ρ (reversePath δ t) * (‖deriv (reversePath δ) t‖₊ : ℝ≥0∞)
      = ∫⁻ t in Set.Icc (0:ℝ) 1, ρ (δ (1 - t)) * (‖deriv δ (1 - t)‖₊ : ℝ≥0∞) := by
    refine lintegral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hbad] with t hbt ht
    have hmem : (1 - t) ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.mem_Icc] at ht
      rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc]
      exact ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
    have hdiff := hbt hmem
    have haff : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
      simpa using! (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
    have hHD : HasDerivAt (reversePath δ) (-1 • deriv δ (1 - t)) t := by
      simpa [reversePath, Function.comp] using! (hdiff.hasDerivAt.scomp t haff)
    change ρ (δ (1 - t)) * (‖deriv (reversePath δ) t‖₊ : ℝ≥0∞)
        = ρ (δ (1 - t)) * (‖deriv δ (1 - t)‖₊ : ℝ≥0∞)
    rw [hHD.deriv]
    congr 2
    simp
  rw [hcong]
  have hG : Measurable (fun u => ρ (δ u) * (‖deriv δ u‖₊ : ℝ≥0∞)) :=
    Measurable.mul (hρ.comp hδcont.measurable) (measurable_deriv δ).nnnorm.coe_nnreal_ennreal
  have hset : (fun x : ℝ => 1 - x) ⁻¹' (Set.Icc (0:ℝ) 1) = Set.Icc (0:ℝ) 1 := by
    ext x; simp only [Set.mem_preimage, Set.mem_Icc]
    exact ⟨fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩,
           fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩⟩
  have hkey := hmp.setLIntegral_comp_preimage (s := Set.Icc (0:ℝ) 1) measurableSet_Icc hG
  rw [hset] at hkey
  exact hkey

/-! ### Point-set topology of the plane-separation core (Brouwer-free)

The lemmas in this section establish the abstract level-continuum existence statement
`rect_level_continuum` via the genuinely two-dimensional boundary-bumping crux `rectLevel_no_split`.
**The entire section is axiom-clean**: the rectangle geometry
(`rectLevel_isCompact_rect`, `rectLevel_isConnected_rect`), the **Šura–Bura quasi-component
separation** (`rectLevel_exists_isClopen_separating`) and component-extraction
(`rectLevel_split_of_no_continuum`), the continuous-argument confinement lemmas
(`confined_{cos,sin}_{pos,neg}_branch`) and the winding contradiction
(`square_crossing_contradiction`), assembled in `rectLevel_no_split` by the gap-threading route.
The sole non-elementary input is the continuous logarithm of a nonvanishing map on the contractible
rectangle (`continuous_log_lift_param_of_continuous_ne_zero`), which is strictly weaker than
Brouwer and already axiom-clean in the repository. -/

/-- The closed coordinate rectangle `[a,b] × [s,t]` in `ℂ` (used only in this section). -/
private def rectLevelRect (a b s t : ℝ) : Set ℂ :=
  {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ (s ≤ z.im ∧ z.im ≤ t)}

/-- The horizontal embedding `x ↦ ⟨x, s⟩` is continuous. -/
private theorem rectLevel_continuous_mk_left (s : ℝ) :
    Continuous (fun x : ℝ => Complex.mk x s) := by
  have : (fun x : ℝ => Complex.mk x s) = (fun x : ℝ => (x : ℂ) + s * Complex.I) := by
    funext x; apply Complex.ext <;> simp
  rw [this]; fun_prop

/-- A single clopen neighbourhood of `x` disjoint from a closed `Q`, given that the connected
component of `x` is disjoint from `Q`. (Compact Hausdorff quasi-component step.) -/
private theorem rectLevel_exists_clopen_nbhd_disjoint {K : Type*} [TopologicalSpace K] [T2Space K]
    [CompactSpace K] {Q : Set K} (hQc : IsClosed Q) {x : K}
    (hxQ : Disjoint (connectedComponent x) Q) :
    ∃ C : Set K, IsClopen C ∧ x ∈ C ∧ Disjoint C Q := by
  rw [connectedComponent_eq_iInter_isClopen x] at hxQ
  have hQcompact : IsCompact Q := hQc.isCompact
  rw [disjoint_iff_inter_eq_empty] at hxQ
  have hempty : (Q ∩ ⋂ s : { s : Set K // IsClopen s ∧ x ∈ s }, (s : Set K)) = ∅ := by
    rw [inter_comm]; exact hxQ
  by_contra hcon
  push Not at hcon
  have hne : (Q ∩ ⋂ s : { s : Set K // IsClopen s ∧ x ∈ s }, (s : Set K)).Nonempty := by
    apply hQcompact.inter_iInter_nonempty
    · intro i; exact i.2.1.1
    · intro u
      set C : Set K := ⋂ i ∈ u, (i : Set K) with hC
      have hCclopen : IsClopen C := by rw [hC]; exact isClopen_biInter_finset (fun i _ => i.2.1)
      have hxC : x ∈ C := by rw [hC]; exact mem_biInter (fun i _ => i.2.2)
      have := hcon C hCclopen hxC
      rw [not_disjoint_iff] at this
      obtain ⟨z, hzC, hzQ⟩ := this
      exact ⟨z, hzQ, hzC⟩
  rw [hempty] at hne
  exact absurd hne (by simp)

/-- **Šura–Bura separation.** In a compact Hausdorff space, if `P` and `Q` are closed and no
preconnected subset meets both, then a clopen set contains `P` and is disjoint from `Q`.

This is the genuinely-missing-from-Mathlib continuum-theory primitive; it is established here
(axiom-clean) from `connectedComponent_eq_iInter_isClopen` plus compactness. -/
private theorem rectLevel_exists_isClopen_separating {K : Type*} [TopologicalSpace K] [T2Space K]
    [CompactSpace K] {P Q : Set K} (hPc : IsClosed P) (hQc : IsClosed Q)
    (hsep : ∀ S : Set K, IsPreconnected S → (S ∩ P).Nonempty → (S ∩ Q).Nonempty → False) :
    ∃ U : Set K, IsClopen U ∧ P ⊆ U ∧ Disjoint U Q := by
  have hcomp : ∀ x ∈ P, Disjoint (connectedComponent x) Q := by
    intro x hxP
    rw [disjoint_iff_inter_eq_empty]
    by_contra hne
    rw [← Ne, ← nonempty_iff_ne_empty] at hne
    exact hsep (connectedComponent x) isConnected_connectedComponent.isPreconnected
      ⟨x, mem_connectedComponent, hxP⟩ hne
  choose! C hCclopen hxC hCQ using fun x (hx : x ∈ P) =>
    rectLevel_exists_clopen_nbhd_disjoint hQc (hcomp x hx)
  have hPcompact : IsCompact P := hPc.isCompact
  obtain ⟨u, husub, hufin, hucover⟩ := hPcompact.elim_finite_subcover_image
    (b := P) (c := C) (fun x hx => (hCclopen x hx).isOpen)
    (fun x hx => mem_biUnion hx (hxC x hx))
  refine ⟨⋃ x ∈ u, C x, ?_, hucover, ?_⟩
  · exact Set.Finite.isClopen_biUnion hufin (fun x hx => hCclopen x (husub hx))
  · rw [Set.disjoint_left]
    rintro z hz hzQ
    rw [mem_iUnion₂] at hz
    obtain ⟨x, hxu, hzCx⟩ := hz
    exact (hCQ x (husub hxu)).le_bot ⟨hzCx, hzQ⟩

/-- `rectLevelRect a b s t` is the product `[a, b] ×ℂ [s, t]`. -/
private theorem rectLevel_rect_eq_reProdIm (a b s t : ℝ) :
    rectLevelRect a b s t = Set.Icc a b ×ℂ Set.Icc s t := by
  ext z; simp only [rectLevelRect, mem_ofPred_eq, Complex.mem_reProdIm, Set.mem_Icc]

/-- The coordinate rectangle `[a, b] × [s, t]` is compact. -/
private theorem rectLevel_isCompact_rect (a b s t : ℝ) : IsCompact (rectLevelRect a b s t) := by
  rw [rectLevel_rect_eq_reProdIm]; exact (isCompact_Icc).reProdIm (isCompact_Icc)

/-- The coordinate rectangle `[a, b] × [s, t]` is closed. -/
private theorem rectLevel_isClosed_rect (a b s t : ℝ) : IsClosed (rectLevelRect a b s t) :=
  (rectLevel_isCompact_rect a b s t).isClosed

/-- The coordinate rectangle `[a, b] × [s, t]` is connected (for `a ≤ b`, `s ≤ t`). -/
private theorem rectLevel_isConnected_rect {a b s t : ℝ} (hab : a ≤ b) (hst : s ≤ t) :
    IsConnected (rectLevelRect a b s t) := by
  have hpre : rectLevelRect a b s t = Complex.equivRealProdCLM.toHomeomorph ⁻¹'
      (Set.Icc a b ×ˢ Set.Icc s t) := by
    ext z
    constructor
    · intro h
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc,
        ContinuousLinearEquiv.coe_toHomeomorph, Complex.equivRealProdCLM_apply]
      exact ⟨⟨h.1.1, h.1.2⟩, ⟨h.2.1, h.2.2⟩⟩
    · intro h
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc,
        ContinuousLinearEquiv.coe_toHomeomorph, Complex.equivRealProdCLM_apply] at h
      exact ⟨⟨h.1.1, h.1.2⟩, ⟨h.2.1, h.2.2⟩⟩
  rw [hpre, Homeomorph.isConnected_preimage]
  exact (isConnected_Icc hab).prod (isConnected_Icc hst)

/-- On the horizontal segment at height `lvl`, the continuous `v` takes every value between its
endpoint values; in particular it attains `c ∈ (0,1)` when the endpoints are `0`, `1` (1-D IVT). -/
private theorem rectLevel_exists_mem_level_on_edge {a b lvl : ℝ} (hab : a ≤ b) {v : ℂ → ℝ}
    (hvcont : Continuous v) (hv0 : v (Complex.mk a lvl) = 0) (hv1 : v (Complex.mk b lvl) = 1)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ x ∈ Set.Icc a b, v (Complex.mk x lvl) = c := by
  have hcont : ContinuousOn (fun x : ℝ => v (Complex.mk x lvl)) (Set.Icc a b) :=
    (hvcont.comp (rectLevel_continuous_mk_left lvl)).continuousOn
  have hsub : Set.Icc (v (Complex.mk a lvl)) (v (Complex.mk b lvl)) ⊆
      (fun x : ℝ => v (Complex.mk x lvl)) '' Set.Icc a b := intermediate_value_Icc hab hcont
  have hcmem : c ∈ Set.Icc (v (Complex.mk a lvl)) (v (Complex.mk b lvl)) := by
    rw [hv0, hv1]; exact ⟨le_of_lt hc.1, le_of_lt hc.2⟩
  obtain ⟨x, hx, hvx⟩ := hsub hcmem
  exact ⟨x, hx, hvx⟩

/-- If a compact `K ⊆ ℂ` has nonempty closed subsets `Bot, Top` not joined by any preconnected
subset of `K`, then `K` splits into two disjoint compacta `K₁ ⊇ Bot`, `K₂ ⊇ Top` with union `K`.
(Šura–Bura in the subtype, pushed to ambient `ℂ`.) -/
private theorem rectLevel_split_of_no_continuum {K Bot Top : Set ℂ} (hK : IsCompact K)
    (hBot : Bot ⊆ K) (hTop : Top ⊆ K) (hBotcl : IsClosed Bot) (hTopcl : IsClosed Top)
    (hsep : ∀ S : Set ℂ, IsPreconnected S → S ⊆ K →
      (S ∩ Bot).Nonempty → (S ∩ Top).Nonempty → False) :
    ∃ K₁ K₂ : Set ℂ, IsCompact K₁ ∧ IsCompact K₂ ∧ Disjoint K₁ K₂ ∧
      K₁ ∪ K₂ = K ∧ Bot ⊆ K₁ ∧ Top ⊆ K₂ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  set P : Set K := Subtype.val ⁻¹' Bot with hP
  set Q : Set K := Subtype.val ⁻¹' Top with hQ
  have hPc : IsClosed P := hBotcl.preimage continuous_subtype_val
  have hQc : IsClosed Q := hTopcl.preimage continuous_subtype_val
  have hsep' : ∀ S : Set K, IsPreconnected S → (S ∩ P).Nonempty → (S ∩ Q).Nonempty → False := by
    intro S hScon hSP hSQ
    refine hsep (Subtype.val '' S) (hScon.image _ continuous_subtype_val.continuousOn)
      (Subtype.coe_image_subset _ _) ?_ ?_
    · obtain ⟨z, hzS, hzP⟩ := hSP
      exact ⟨z.1, ⟨z, hzS, rfl⟩, hzP⟩
    · obtain ⟨z, hzS, hzQ⟩ := hSQ
      exact ⟨z.1, ⟨z, hzS, rfl⟩, hzQ⟩
  obtain ⟨U, hUclopen, hPU, hUQ⟩ := rectLevel_exists_isClopen_separating hPc hQc hsep'
  refine ⟨Subtype.val '' U, Subtype.val '' Uᶜ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hUclopen.1.isCompact).image continuous_subtype_val
  · exact (hUclopen.compl.1.isCompact).image continuous_subtype_val
  · rw [Set.disjoint_left]
    rintro z ⟨x, hxU, rfl⟩ ⟨y, hyU, hxy⟩
    have : y = x := Subtype.val_injective hxy
    rw [this] at hyU; exact hyU hxU
  · rw [← Set.image_union, Set.union_compl_self, Set.image_univ, Subtype.range_coe]
  · intro z hz
    have hzK : z ∈ K := hBot hz
    refine ⟨⟨z, hzK⟩, hPU ?_, rfl⟩; simpa [hP] using hz
  · intro z hz
    have hzK : z ∈ K := hTop hz
    refine ⟨⟨z, hzK⟩, ?_, rfl⟩
    have hzQ : (⟨z, hzK⟩ : K) ∈ Q := by simpa [hQ] using hz
    rw [Set.mem_compl_iff]
    intro hzU; exact (Set.disjoint_left.mp hUQ hzU) hzQ

/-! ### Continuous-argument confinement and the square-crossing winding contradiction

The lemmas below provide the genuinely two-dimensional ingredient of the boundary-bumping crux,
**Brouwer-free**: a single-valued continuous argument `θ` on the rectangle whose cosine/sine are
sign-constrained on the four edges (`Im φ > 0` on the bottom, `Re φ > 0` on the right, `Im φ < 0`
on the top, `Re φ < 0` on the left) is impossible, because the four half-plane confinements force a
net winding of `±2π` while single-valuedness forces winding `0`. The only non-elementary input is
the **continuous logarithm** of a nonvanishing map on the (simply connected) rectangle, which is the
axiom-clean `continuous_log_lift_param_of_continuous_ne_zero`; the confinement
lemmas themselves are pure 1-D intermediate-value arguments. -/

/-- A continuous real function on `[p, q]` whose cosine is everywhere positive cannot move by `π`
or more between the endpoints (its image stays in a single `cos`-positive open branch). -/
private theorem confined_cos_pos {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hcos : ∀ u ∈ Set.Icc p q, 0 < Real.cos (f u)) :
    |f q - f p| < π := by
  by_contra hcon
  rw [not_lt] at hcon  -- π ≤ |f q - f p|
  set lo := min (f p) (f q) with hlo
  set hi := max (f p) (f q) with hhi
  have hlen : π ≤ hi - lo := by
    rw [hlo, hhi]
    rcases le_total (f p) (f q) with h | h
    · rw [max_eq_right h, min_eq_left h]
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ f q - f p)] at hcon; linarith
    · rw [max_eq_left h, min_eq_right h]
      rw [abs_of_nonpos (by linarith : f q - f p ≤ 0)] at hcon; linarith
  set k : ℤ := ⌈ lo / π - 1/2 ⌉ with hk
  set c : ℝ := (2 * (k:ℝ) + 1) * π / 2 with hc
  have hpi : 0 < π := Real.pi_pos
  have hc_ge_lo : lo ≤ c := by
    have h1 : lo / π - 1/2 ≤ (k:ℝ) := Int.le_ceil _
    have : lo / π ≤ (k:ℝ) + 1/2 := by linarith
    have h2 : lo ≤ ((k:ℝ) + 1/2) * π := by
      rw [div_le_iff₀ hpi] at this; linarith
    rw [hc]; nlinarith
  have hc_le_hi : c ≤ hi := by
    have h1 : (k:ℝ) < lo / π - 1/2 + 1 := Int.ceil_lt_add_one _
    have h2 : (k:ℝ) + 1/2 < lo / π + 1 := by linarith
    have h3 : ((k:ℝ) + 1/2) * π < (lo / π + 1) * π :=
      mul_lt_mul_of_pos_right h2 hpi
    have h4 : (lo / π + 1) * π = lo + π := by field_simp
    have hclt : c < lo + π := by rw [hc]; nlinarith [h3, h4]
    linarith [hlen]
  have hcos_c : Real.cos c = 0 := by
    rw [Real.cos_eq_zero_iff]; exact ⟨k, by rw [hc]⟩
  have hc_mem : c ∈ Set.uIcc (f p) (f q) := by
    rw [Set.mem_uIcc]
    rcases le_total (f p) (f q) with h | h
    · left; refine ⟨?_, ?_⟩
      · have : lo = f p := min_eq_left h; rw [← this]; exact hc_ge_lo
      · have : hi = f q := max_eq_right h; rw [← this]; exact hc_le_hi
    · right; refine ⟨?_, ?_⟩
      · have : lo = f q := min_eq_right h; rw [← this]; exact hc_ge_lo
      · have : hi = f p := max_eq_left h; rw [← this]; exact hc_le_hi
  have huIcc : Set.uIcc p q = Set.Icc p q := Set.uIcc_of_le hpq
  have hf' : ContinuousOn f (Set.uIcc p q) := by rw [huIcc]; exact hf
  obtain ⟨u, hu_mem, hu_eq⟩ := intermediate_value_uIcc hf' hc_mem
  rw [huIcc] at hu_mem
  have : 0 < Real.cos c := hu_eq ▸ hcos u hu_mem
  rw [hcos_c] at this
  exact lt_irrefl 0 this

/-- `sin > 0` confinement (bottom edge): obtained from `confined_cos_pos` by a `π/2` phase shift. -/
private theorem confined_sin_pos {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hsin : ∀ u ∈ Set.Icc p q, 0 < Real.sin (f u)) :
    |f q - f p| < π := by
  have key := confined_cos_pos hpq (f := fun u => f u - π/2)
    ((hf.sub continuousOn_const)) ?_
  · have : (f q - π/2) - (f p - π/2) = f q - f p := by ring
    rwa [this] at key
  · intro u hu
    have : Real.cos (f u - π/2) = Real.sin (f u) := by
      rw [show f u - π/2 = -(π/2 - f u) by ring, Real.cos_neg, Real.cos_pi_div_two_sub]
    rw [this]; exact hsin u hu

/-- `sin < 0` confinement (top edge). -/
private theorem confined_sin_neg {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hsin : ∀ u ∈ Set.Icc p q, Real.sin (f u) < 0) :
    |f q - f p| < π := by
  have key := confined_cos_pos hpq (f := fun u => f u + π/2)
    ((hf.add continuousOn_const)) ?_
  · have : (f q + π/2) - (f p + π/2) = f q - f p := by ring
    rwa [this] at key
  · intro u hu
    have : Real.cos (f u + π/2) = -Real.sin (f u) := Real.cos_add_pi_div_two (f u)
    rw [this]; linarith [hsin u hu]

/-- `cos < 0` confinement (left edge). -/
private theorem confined_cos_neg {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hcos : ∀ u ∈ Set.Icc p q, Real.cos (f u) < 0) :
    |f q - f p| < π := by
  have key := confined_cos_pos hpq (f := fun u => f u + π)
    ((hf.add continuousOn_const)) ?_
  · have : (f q + π) - (f p + π) = f q - f p := by ring
    rwa [this] at key
  · intro u hu
    have : Real.cos (f u + π) = -Real.cos (f u) := Real.cos_add_pi (f u)
    rw [this]; linarith [hcos u hu]

/-- Branch characterization of `cos x > 0`: `x` lies in a unique open interval
`(2πk - π/2, 2πk + π/2)`. -/
private theorem cos_pos_branch {x : ℝ} (hx : 0 < Real.cos x) :
    ∃ k : ℤ, x ∈ Set.Ioo (2 * π * k - π/2) (2 * π * k + π/2) := by
  have hpi : 0 < π := Real.pi_pos
  set n : ℤ := ⌊ x/π + 1/2 ⌋ with hn
  have hfloor_le : (n:ℝ) ≤ x/π + 1/2 := Int.floor_le _
  have hlt_floor : x/π + 1/2 < n + 1 := Int.lt_floor_add_one _
  have hdiv : x / π * π = x := div_mul_cancel₀ x (ne_of_gt hpi)
  have hxlo : (n:ℝ) * π - π/2 ≤ x := by
    have := mul_le_mul_of_nonneg_right hfloor_le (le_of_lt hpi)
    rw [add_mul, hdiv] at this; nlinarith [this]
  have hxhi : x < (n:ℝ) * π + π/2 := by
    have := mul_lt_mul_of_pos_right hlt_floor hpi
    rw [add_mul, hdiv] at this; nlinarith [this]
  have hcosfac : Real.cos x = (-1)^n * Real.cos (x - n * π) := by
    have : x = (x - n*π) + n*π := by ring
    rw [this, Real.cos_add_int_mul_pi]; ring_nf
  have hxlo' : (n:ℝ) * π - π/2 < x := by
    rcases lt_or_eq_of_le hxlo with h | h
    · exact h
    · exfalso
      have hcosx0 : Real.cos x = 0 := by
        rw [← h, Real.cos_eq_zero_iff]; exact ⟨n - 1, by push_cast; ring⟩
      rw [hcosx0] at hx; exact lt_irrefl 0 hx
  have hcos_t : 0 < Real.cos (x - n*π) := by
    apply Real.cos_pos_of_mem_Ioo
    rw [Set.mem_Ioo]
    refine ⟨?_, ?_⟩
    · nlinarith [hxlo']
    · nlinarith [hxhi]
  have hsign : (0:ℝ) < (-1:ℝ)^n := by
    rcases lt_trichotomy ((-1:ℝ)^n) 0 with h | h | h
    · exfalso; nlinarith [hcosfac, hx, hcos_t, mul_neg_of_neg_of_pos h hcos_t]
    · exfalso; rw [hcosfac, h, zero_mul] at hx; exact lt_irrefl 0 hx
    · exact h
  have hneven : Even n := by
    rcases Int.even_or_odd n with he | ho
    · exact he
    · exfalso; rw [ho.neg_one_zpow] at hsign; norm_num at hsign
  obtain ⟨k, hk⟩ := hneven
  have hnk : (n:ℝ) = 2 * k := by rw [hk]; push_cast; ring
  refine ⟨k, ?_, ?_⟩
  · rw [hnk] at hxlo'; nlinarith [hxlo']
  · rw [hnk] at hxhi; nlinarith [hxhi]

/-- A continuous `f` on `[p, q]` with `cos∘f > 0` everywhere lies in a single open
`cos`-positive branch `(2πk - π/2, 2πk + π/2)`. -/
private theorem confined_cos_pos_branch {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hcos : ∀ u ∈ Set.Icc p q, 0 < Real.cos (f u)) :
    ∃ k : ℤ, ∀ u ∈ Set.Icc p q, f u ∈ Set.Ioo (2 * π * k - π/2) (2 * π * k + π/2) := by
  have hpi : 0 < π := Real.pi_pos
  have hp_mem : p ∈ Set.Icc p q := Set.left_mem_Icc.mpr hpq
  obtain ⟨k, hk⟩ := cos_pos_branch (hcos p hp_mem)
  refine ⟨k, fun u hu => ?_⟩
  obtain ⟨k', hk'⟩ := cos_pos_branch (hcos u hu)
  have hpu : p ≤ u := hu.1
  have hsub : Set.Icc p u ⊆ Set.Icc p q := Set.Icc_subset_Icc le_rfl hu.2
  have hbnd : |f u - f p| < π :=
    confined_cos_pos hpu (hf.mono hsub) (fun w hw => hcos w (hsub hw))
  rw [abs_lt] at hbnd
  have hkeq : k' = k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hk'le : (k':ℝ) ≤ (k:ℝ) - 1 := by
        have : k' ≤ k - 1 := by omega
        exact_mod_cast this
      have h1 : f u < 2 * π * k' + π/2 := hk'.2
      have h2 : 2 * π * k - π/2 < f p := hk.1
      nlinarith [hbnd.1, h1, h2, hk'le, hpi]
    · have hkle : (k:ℝ) ≤ (k':ℝ) - 1 := by
        have : k ≤ k' - 1 := by omega
        exact_mod_cast this
      have h1 : 2 * π * k' - π/2 < f u := hk'.1
      have h2 : f p < 2 * π * k + π/2 := hk.2
      nlinarith [hbnd.2, h1, h2, hkle, hpi]
  rw [← hkeq]; exact hk'

/-- Branch confinement `sin > 0`: branch `(2πk, 2πk + π)`. -/
private theorem confined_sin_pos_branch {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hsin : ∀ u ∈ Set.Icc p q, 0 < Real.sin (f u)) :
    ∃ k : ℤ, ∀ u ∈ Set.Icc p q, f u ∈ Set.Ioo (2 * π * k) (2 * π * k + π) := by
  obtain ⟨k, hk⟩ := confined_cos_pos_branch hpq (f := fun u => f u - π/2)
    (hf.sub continuousOn_const)
    (fun u hu => by
      have : Real.cos (f u - π/2) = Real.sin (f u) := by
        rw [show f u - π/2 = -(π/2 - f u) by ring, Real.cos_neg, Real.cos_pi_div_two_sub]
      rw [this]; exact hsin u hu)
  refine ⟨k, fun u hu => ?_⟩
  have := hk u hu
  rw [Set.mem_Ioo] at this ⊢
  constructor <;> [nlinarith [this.1]; nlinarith [this.2]]

/-- Branch confinement `sin < 0`: branch `(2πk - π, 2πk)`. -/
private theorem confined_sin_neg_branch {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hsin : ∀ u ∈ Set.Icc p q, Real.sin (f u) < 0) :
    ∃ k : ℤ, ∀ u ∈ Set.Icc p q, f u ∈ Set.Ioo (2 * π * k - π) (2 * π * k) := by
  obtain ⟨k, hk⟩ := confined_cos_pos_branch hpq (f := fun u => f u + π/2)
    (hf.add continuousOn_const)
    (fun u hu => by
      have : Real.cos (f u + π/2) = -Real.sin (f u) := Real.cos_add_pi_div_two (f u)
      rw [this]; linarith [hsin u hu])
  refine ⟨k, fun u hu => ?_⟩
  have := hk u hu
  rw [Set.mem_Ioo] at this ⊢
  constructor <;> [nlinarith [this.1]; nlinarith [this.2]]

/-- Branch confinement `cos < 0`: branch `(2πk + π/2, 2πk + 3π/2)`. -/
private theorem confined_cos_neg_branch {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hcos : ∀ u ∈ Set.Icc p q, Real.cos (f u) < 0) :
    ∃ k : ℤ, ∀ u ∈ Set.Icc p q, f u ∈ Set.Ioo (2 * π * k + π/2) (2 * π * k + 3*π/2) := by
  obtain ⟨k, hk⟩ := confined_cos_pos_branch hpq (f := fun u => f u - π)
    (hf.sub continuousOn_const)
    (fun u hu => by
      have : Real.cos (f u - π) = -Real.cos (f u) := by
        rw [show f u - π = -(π - f u) by ring, Real.cos_neg, Real.cos_pi_sub]
      rw [this]; linarith [hcos u hu])
  refine ⟨k, fun u hu => ?_⟩
  have := hk u hu
  rw [Set.mem_Ioo] at this ⊢
  constructor <;> [nlinarith [this.1]; nlinarith [this.2]]

/-- **Square-crossing winding contradiction.** A single-valued continuous argument `θ` on the
rectangle `[a,b] × [s,t]` (`a ≤ b`, `s ≤ t`) whose `sin/cos` are sign-constrained on the four
edges — `sin (θ · s) > 0` on the bottom, `cos (θ b ·) > 0` on the right, `sin (θ · t) < 0` on the
top, `cos (θ a ·) < 0` on the left — is impossible: the four half-plane confinements force a winding
of `2π`, contradicting single-valuedness. (No Brouwer; pure 1-D intermediate-value argument.) -/
private theorem square_crossing_contradiction {a b s t : ℝ} (hab : a ≤ b) (hst : s ≤ t)
    (θ : ℝ → ℝ → ℝ)
    (hbot : ContinuousOn (fun x => θ x s) (Set.Icc a b))
    (hrgt : ContinuousOn (fun y => θ b y) (Set.Icc s t))
    (htop : ContinuousOn (fun x => θ x t) (Set.Icc a b))
    (hlft : ContinuousOn (fun y => θ a y) (Set.Icc s t))
    (Hbot : ∀ x ∈ Set.Icc a b, 0 < Real.sin (θ x s))
    (Hrgt : ∀ y ∈ Set.Icc s t, 0 < Real.cos (θ b y))
    (Htop : ∀ x ∈ Set.Icc a b, Real.sin (θ x t) < 0)
    (Hlft : ∀ y ∈ Set.Icc s t, Real.cos (θ a y) < 0) :
    False := by
  have hpi : 0 < π := Real.pi_pos
  set A := θ a s with hA
  set B := θ b s with hB
  set C := θ b t with hC
  set D := θ a t with hD
  have ha_mem_ab : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hb_mem_ab : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  have hs_mem_st : s ∈ Set.Icc s t := Set.left_mem_Icc.mpr hst
  have ht_mem_st : t ∈ Set.Icc s t := Set.right_mem_Icc.mpr hst
  obtain ⟨kb, hkb⟩ := confined_sin_pos_branch hab hbot Hbot
  obtain ⟨kr, hkr⟩ := confined_cos_pos_branch hst hrgt Hrgt
  obtain ⟨kt, hkt⟩ := confined_sin_neg_branch hab htop Htop
  obtain ⟨kl, hkl⟩ := confined_cos_neg_branch hst hlft Hlft
  have hA_bot : A ∈ Set.Ioo (2*π*kb) (2*π*kb + π) := hkb a ha_mem_ab
  have hA_lft : A ∈ Set.Ioo (2*π*kl + π/2) (2*π*kl + 3*π/2) := hkl s hs_mem_st
  have hB_bot : B ∈ Set.Ioo (2*π*kb) (2*π*kb + π) := hkb b hb_mem_ab
  have hB_rgt : B ∈ Set.Ioo (2*π*kr - π/2) (2*π*kr + π/2) := hkr s hs_mem_st
  have hC_rgt : C ∈ Set.Ioo (2*π*kr - π/2) (2*π*kr + π/2) := hkr t ht_mem_st
  have hC_top : C ∈ Set.Ioo (2*π*kt - π) (2*π*kt) := hkt b hb_mem_ab
  have hD_top : D ∈ Set.Ioo (2*π*kt - π) (2*π*kt) := hkt a ha_mem_ab
  have hD_lft : D ∈ Set.Ioo (2*π*kl + π/2) (2*π*kl + 3*π/2) := hkl t ht_mem_st
  rw [Set.mem_Ioo] at hA_bot hA_lft hB_bot hB_rgt hC_rgt hC_top hD_top hD_lft
  have int_le : ∀ i j : ℤ, (i:ℝ) < (j:ℝ) + 1 → i ≤ j := by
    intro i j h
    have : i < j + 1 := by exact_mod_cast h
    omega
  have e_kb_le_kr : kb ≤ kr := by
    apply int_le; nlinarith [hB_bot.1, hB_rgt.2, hpi]
  have e_kr_le_kb : kr ≤ kb := by
    apply int_le; nlinarith [hB_rgt.1, hB_bot.2, hpi]
  have hkr' : (kr:ℝ) = (kb:ℝ) := by
    have : kr = kb := le_antisymm e_kr_le_kb e_kb_le_kr; exact_mod_cast this
  have e_kb_le_kt : kb ≤ kt := by
    apply int_le; nlinarith [hC_rgt.1, hC_top.2, hpi, hkr']
  have e_kt_le_kb : kt ≤ kb := by
    apply int_le; nlinarith [hC_top.1, hC_rgt.2, hpi, hkr']
  have hkt' : (kt:ℝ) = (kb:ℝ) := by
    have : kt = kb := le_antisymm e_kt_le_kb e_kb_le_kt; exact_mod_cast this
  have e_kl_le : kl ≤ kb - 1 := by
    apply int_le
    have hlt : (kl:ℝ) < kb := by nlinarith [hD_lft.1, hD_top.2, hpi, hkt']
    push_cast; linarith
  have e_kl_ge : kb - 1 ≤ kl := by
    apply int_le
    have hlt : (kb:ℝ) < kl + 2 := by nlinarith [hD_top.1, hD_lft.2, hpi, hkt']
    push_cast; linarith
  have hkl' : (kl:ℝ) = (kb:ℝ) - 1 := by
    have : kl = kb - 1 := le_antisymm e_kl_le e_kl_ge; rw [this]; push_cast; ring
  have hAlo : 2*π*(kb:ℝ) < A := hA_bot.1
  have hAhi : A < 2*π*(kl:ℝ) + 3*π/2 := hA_lft.2
  nlinarith [hAlo, hAhi, hpi, hkl']

/-- **The boundary-bumping crux (the genuinely two-dimensional plane-separation core).**

With `Rect = [a,b]×[s,t]`, continuous `v` with `v = 0` on the left edge `{re = a}` and `v = 1` on
the right edge `{re = b}`, and `c ∈ (0,1)`, the level set `K = Rect ∩ {v = c}` **cannot** have its
bottom points `{im = s} ∩ K` topologically separated from its top points `{im = t} ∩ K`: there is
*always* a preconnected subset of `K` meeting both the bottom and the top edge. Equivalently
(contrapositive, the form used here): if **no** preconnected `S ⊆ K` meets both the bottom edge
`{im = s}` and the top edge `{im = t}`, that is a contradiction.

## Proof (Brouwer-free, axiom-clean)

This is the classical Steinhaus-chessboard / Šura–Bura plane-separation core. It is established here
**without** any Brouwer / Jordan / topological-degree input, by the *gap-threading winding* route:

1. **Šura–Bura split** (`rectLevel_split_of_no_continuum`): the contradiction hypothesis `hsep`
   gives a clopen-in-`K` decomposition `K = K₁ ⊔ K₂` with `Bot ⊆ K₁`, `Top ⊆ K₂`.
2. **Urysohn separator** (`exists_continuous_zero_one_of_isClosed`, `ℂ` normal): the disjoint
   closed sets `P = K₁ ∪ (full bottom edge)` and `Q = K₂ ∪ (full top edge)` (disjointness uses the
   split inclusions and `s < t`) carry a continuous `η : ℂ → ℝ` with `η = +1` on `P`, `η = −1`
   on `Q`.
3. **Nonvanishing field**: `φ z = (v z − c) + i·η z` is nonvanishing on `Rect` (if `v z = c` then
   `z ∈ K = K₁ ∪ K₂`, where `η = ±1 ≠ 0`), with the four-edge sign pattern `Re φ < 0` (left,
   `v = 0`), `Re φ > 0` (right, `v = 1`), `Im φ > 0` (bottom, `η = +1`), `Im φ < 0` (top, `η = −1`).
4. **Continuous logarithm**: since `Rect` is contractible, `φ` admits a global continuous log
   (`continuous_log_lift_param_of_continuous_ne_zero`, the repository's axiom-clean
   covering-space lift), so `θ := Im(L)` is a single-valued continuous argument of `φ`.
5. **Winding contradiction** (`square_crossing_contradiction`): the four-edge sign pattern confines
   `θ` to consecutive half-plane branches whose corner-matching forces a net winding of `2π`,
   contradicting that `θ` is single-valued. Each confinement is a pure 1-D intermediate-value
   argument (`confined_{cos,sin}_{pos,neg}_branch`).

The only non-elementary ingredient is the continuous logarithm of step 4, which is strictly weaker
than Brouwer (it is the *absence* of a degree obstruction on the contractible square) and is already
axiom-clean in the repository. -/
private theorem rectLevel_no_split {a b s t : ℝ} (hab : a ≤ b) (hst : s ≤ t)
    {v : ℂ → ℝ} (hvcont : Continuous v)
    (hv0 : ∀ z : ℂ, z.re = a → s ≤ z.im → z.im ≤ t → v z = 0)
    (hv1 : ∀ z : ℂ, z.re = b → s ≤ z.im → z.im ≤ t → v z = 1)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hsep : ∀ S : Set ℂ, IsPreconnected S → S ⊆ rectLevelRect a b s t ∩ v ⁻¹' {c} →
      (∃ p ∈ S, p.im = s) → (∃ q ∈ S, q.im = t) → False) :
    False := by
  have hpi : 0 < π := Real.pi_pos
  set R : Set ℂ := rectLevelRect a b s t with hR
  set K : Set ℂ := R ∩ v ⁻¹' {c} with hKdef
  -- The full bottom/top edges of the rectangle (closed segments at heights `s`, `t`).
  set botEdge : Set ℂ := {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ z.im = s} with hbotEdge
  set topEdge : Set ℂ := {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ z.im = t} with htopEdge
  -- Membership helpers in `mk` coordinates.
  have hmk_re : ∀ x y : ℝ, (Complex.mk x y).re = x := fun _ _ => rfl
  have hmk_im : ∀ x y : ℝ, (Complex.mk x y).im = y := fun _ _ => rfl
  -- `v` restricted to a horizontal segment.
  -- Degenerate case `s = t`: the rectangle is a single segment; 1-D IVT finds a level point and
  -- a one-point preconnected `S` violates `hsep`.
  rcases eq_or_lt_of_le hst with hst_eq | hst_lt
  · obtain ⟨x, hx_mem, hvx⟩ := rectLevel_exists_mem_level_on_edge hab hvcont
      (hv0 (Complex.mk a s) rfl (le_refl s) hst) (hv1 (Complex.mk b s) rfl (le_refl s) hst) hc
    refine hsep {Complex.mk x s} isPreconnected_singleton ?_ ⟨_, rfl, rfl⟩
      ⟨_, rfl, hst_eq⟩
    rintro z hz; rw [Set.mem_singleton_iff] at hz; subst hz
    refine ⟨⟨⟨hx_mem.1, hx_mem.2⟩, le_refl s, hst⟩, ?_⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hvx
  -- Main case `s < t`. Set up the bottom/top level point sets.
  set Bot : Set ℂ := {z ∈ K | z.im = s} with hBotdef
  set Top : Set ℂ := {z ∈ K | z.im = t} with hTopdef
  have hRcompact : IsCompact R := rectLevel_isCompact_rect a b s t
  have hvc_closed : IsClosed (v ⁻¹' {c}) := (isClosed_singleton).preimage hvcont
  have hKcompact : IsCompact K := hRcompact.inter_right hvc_closed
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hBot_sub : Bot ⊆ K := fun z hz => hz.1
  have hTop_sub : Top ⊆ K := fun z hz => hz.1
  have hBot_closed : IsClosed Bot := by
    have : Bot = K ∩ {z : ℂ | z.im = s} :=
      Set.ext fun z => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
    rw [this]; exact hKclosed.inter (isClosed_eq Complex.continuous_im continuous_const)
  have hTop_closed : IsClosed Top := by
    have : Top = K ∩ {z : ℂ | z.im = t} :=
      Set.ext fun z => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
    rw [this]; exact hKclosed.inter (isClosed_eq Complex.continuous_im continuous_const)
  -- Šura–Bura split: `K = K₁ ⊔ K₂` with `Bot ⊆ K₁`, `Top ⊆ K₂`.
  have hsep_split : ∀ S : Set ℂ, IsPreconnected S → S ⊆ K →
      (S ∩ Bot).Nonempty → (S ∩ Top).Nonempty → False := by
    intro S hScon hSK hSB hST
    refine hsep S hScon hSK ?_ ?_
    · obtain ⟨p, hpS, hpBot⟩ := hSB; exact ⟨p, hpS, hpBot.2⟩
    · obtain ⟨q, hqS, hqTop⟩ := hST; exact ⟨q, hqS, hqTop.2⟩
  obtain ⟨K₁, K₂, hK₁cpt, hK₂cpt, hK₁₂disj, hK₁₂union, hBotK₁, hTopK₂⟩ :=
    rectLevel_split_of_no_continuum hKcompact hBot_sub hTop_sub hBot_closed hTop_closed hsep_split
  have hK₁closed : IsClosed K₁ := hK₁cpt.isClosed
  have hK₂closed : IsClosed K₂ := hK₂cpt.isClosed
  -- Edge closedness.
  have hbotEdge_closed : IsClosed botEdge := by
    have : botEdge = {z : ℂ | a ≤ z.re} ∩ {z : ℂ | z.re ≤ b} ∩ {z : ℂ | z.im = s} := by
      ext z; simp only [hbotEdge, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
    rw [this]
    exact ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)).inter
      (isClosed_eq Complex.continuous_im continuous_const)
  have htopEdge_closed : IsClosed topEdge := by
    have : topEdge = {z : ℂ | a ≤ z.re} ∩ {z : ℂ | z.re ≤ b} ∩ {z : ℂ | z.im = t} := by
      ext z; simp only [htopEdge, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
    rw [this]
    exact ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)).inter
      (isClosed_eq Complex.continuous_im continuous_const)
  -- The two Urysohn sets `P = K₁ ∪ botEdge`, `Q = K₂ ∪ topEdge`.
  set P : Set ℂ := K₁ ∪ botEdge with hPdef
  set Q : Set ℂ := K₂ ∪ topEdge with hQdef
  have hP_closed : IsClosed P := hK₁closed.union hbotEdge_closed
  have hQ_closed : IsClosed Q := hK₂closed.union htopEdge_closed
  -- `K ⊆ K₁ ∪ K₂` (from the union equality) and the edge ⊆ K facts via level membership.
  have hbotEdge_K : ∀ z ∈ botEdge, z ∈ K → z ∈ K₁ := by
    intro z hz hzK; exact hBotK₁ ⟨hzK, hz.2⟩
  have htopEdge_K : ∀ z ∈ topEdge, z ∈ K → z ∈ K₂ := by
    intro z hz hzK; exact hTopK₂ ⟨hzK, hz.2⟩
  -- `P` and `Q` are disjoint.
  have hPQ_disj : Disjoint P Q := by
    rw [Set.disjoint_left]
    rintro z hzP hzQ
    rcases hzP with hzK₁ | hzbot <;> rcases hzQ with hzK₂ | hztop
    · exact (Set.disjoint_left.mp hK₁₂disj hzK₁) hzK₂
    · -- z ∈ K₁ and z ∈ topEdge: z.im = t and z ∈ K₁ ⊆ K, so z ∈ Top ⊆ K₂; contradiction.
      have hzK : z ∈ K := hK₁₂union ▸ Set.mem_union_left _ hzK₁
      exact (Set.disjoint_left.mp hK₁₂disj hzK₁) (htopEdge_K z hztop hzK)
    · -- z ∈ botEdge and z ∈ K₂: z.im = s and z ∈ K₂ ⊆ K, so z ∈ Bot ⊆ K₁; contradiction.
      have hzK : z ∈ K := hK₁₂union ▸ Set.mem_union_right _ hzK₂
      exact (Set.disjoint_left.mp hK₁₂disj (hbotEdge_K z hzbot hzK)) hzK₂
    · -- z ∈ botEdge ∩ topEdge: z.im = s and z.im = t with s < t.
      rw [hbotEdge, Set.mem_ofPred_eq] at hzbot
      rw [htopEdge, Set.mem_ofPred_eq] at hztop
      exact absurd (hzbot.2.symm.trans hztop.2) (ne_of_lt hst_lt)
  -- Urysohn function: `g = 0` on `P`, `g = 1` on `Q`, `g ∈ [0,1]`.
  obtain ⟨g, hgP, hgQ, hg01⟩ := exists_continuous_zero_one_of_isClosed hP_closed hQ_closed hPQ_disj
  -- `η = 1 - 2 g`: `η = 1` on `P`, `η = -1` on `Q`.
  set η : ℂ → ℝ := fun z => 1 - 2 * g z with hηdef
  have hη_cont : Continuous η := by fun_prop
  have hηP : ∀ z ∈ P, η z = 1 := by
    intro z hz
    have : g z = 0 := by have := hgP hz; simpa using this
    simp only [hηdef]; rw [this]; ring
  have hηQ : ∀ z ∈ Q, η z = -1 := by
    intro z hz
    have : g z = 1 := by have := hgQ hz; simpa using this
    simp only [hηdef]; rw [this]; ring
  -- The nonvanishing map `φ z = (v z - c) + i η z`.
  set φ : ℂ → ℂ := fun z => Complex.mk (v z - c) (η z) with hφdef
  have hφ_cont : Continuous φ := by
    have : φ = fun z => ((v z - c : ℝ) : ℂ) + (η z : ℝ) * Complex.I := by
      funext z; apply Complex.ext <;> simp [hφdef]
    rw [this]; fun_prop
  -- `φ z ≠ 0` for `z ∈ R`.
  have hφ_ne : ∀ z ∈ R, φ z ≠ 0 := by
    intro z hzR hφ0
    have hre0 : (φ z).re = 0 := by rw [hφ0]; rfl
    have him0 : (φ z).im = 0 := by rw [hφ0]; rfl
    have hvz : v z = c := by
      have : v z - c = 0 := by simpa [hφdef, hmk_re] using hre0
      linarith
    have hzK : z ∈ K := ⟨hzR, by rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hvz⟩
    have hηz0 : η z = 0 := by simpa [hφdef, hmk_im] using him0
    rcases (hK₁₂union ▸ hzK : z ∈ K₁ ∪ K₂) with hzK₁ | hzK₂
    · have : η z = 1 := hηP z (Set.mem_union_left _ hzK₁)
      rw [hηz0] at this; norm_num at this
    · have : η z = -1 := hηQ z (Set.mem_union_left _ hzK₂)
      rw [hηz0] at this; norm_num at this
  -- The parametrized nonvanishing map and its continuous logarithm.
  set u : ℝ → ℝ → ℂ := fun x y => φ (Complex.mk x y) with hudef
  have hmk2_cont : Continuous (fun p : ℝ × ℝ => Complex.mk p.1 p.2) := by
    have : (fun p : ℝ × ℝ => Complex.mk p.1 p.2)
        = fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) + (p.2 : ℝ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [this]; fun_prop
  have hu_cont : ContinuousOn (Function.uncurry u) (Set.Icc a b ×ˢ Set.Icc s t) := by
    have : Function.uncurry u = fun p : ℝ × ℝ => φ (Complex.mk p.1 p.2) := by
      funext p; simp [Function.uncurry, hudef]
    rw [this]; exact (hφ_cont.comp hmk2_cont).continuousOn
  -- A point of the box lies in `R`.
  have hmk_mem_R : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc s t, Complex.mk x y ∈ R := by
    intro x hx y hy
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hmk_re]; exact hx.1
    · rw [hmk_re]; exact hx.2
    · rw [hmk_im]; exact hy.1
    · rw [hmk_im]; exact hy.2
  have hu_ne : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc s t, u x y ≠ 0 := by
    intro x hx y hy; exact hφ_ne _ (hmk_mem_R x hx y hy)
  obtain ⟨L, hL_cont, hL_exp⟩ :=
    continuous_log_lift_param_of_continuous_ne_zero hab hst u hu_cont hu_ne
  -- The single-valued argument `θ x y = (L x y).im`.
  set θ : ℝ → ℝ → ℝ := fun x y => (L x y).im with hθdef
  -- Sign of `Re/Im (φ (mk x y)) = exp((L x y).re) · cos/sin (θ x y)`.
  have hsign : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc s t,
      (v (Complex.mk x y) - c = Real.exp ((L x y).re) * Real.cos (θ x y)) ∧
      (η (Complex.mk x y) = Real.exp ((L x y).re) * Real.sin (θ x y)) := by
    intro x hx y hy
    have hexp : Complex.exp (L x y) = u x y := hL_exp x hx y hy
    have hre : (u x y).re = Real.exp ((L x y).re) * Real.cos (θ x y) := by
      rw [← hexp, Complex.exp_re]
    have him : (u x y).im = Real.exp ((L x y).re) * Real.sin (θ x y) := by
      rw [← hexp, Complex.exp_im]
    refine ⟨?_, ?_⟩
    · have : (u x y).re = v (Complex.mk x y) - c := by simp [hudef, hφdef, hmk_re]
      rw [this] at hre; exact hre
    · have : (u x y).im = η (Complex.mk x y) := by simp [hudef, hφdef, hmk_im]
      rw [this] at him; exact him
  -- Continuity of `θ` along the four edges.
  have hLuncurry : Continuous (Function.uncurry L) := hL_cont
  have hθ_cont_uncurry : Continuous (Function.uncurry θ) := by
    have : Function.uncurry θ = fun p : ℝ × ℝ => (Function.uncurry L p).im := by
      funext p; simp [hθdef, Function.uncurry]
    rw [this]; exact Complex.continuous_im.comp hLuncurry
  have hbot_cont : ContinuousOn (fun x => θ x s) (Set.Icc a b) := by
    have : (fun x => θ x s) = (Function.uncurry θ) ∘ (fun x : ℝ => (x, s)) := by
      funext x; simp [Function.uncurry]
    rw [this]; exact (hθ_cont_uncurry.comp (by fun_prop)).continuousOn
  have hrgt_cont : ContinuousOn (fun y => θ b y) (Set.Icc s t) := by
    have : (fun y => θ b y) = (Function.uncurry θ) ∘ (fun y : ℝ => (b, y)) := by
      funext y; simp [Function.uncurry]
    rw [this]; exact (hθ_cont_uncurry.comp (by fun_prop)).continuousOn
  have htop_cont : ContinuousOn (fun x => θ x t) (Set.Icc a b) := by
    have : (fun x => θ x t) = (Function.uncurry θ) ∘ (fun x : ℝ => (x, t)) := by
      funext x; simp [Function.uncurry]
    rw [this]; exact (hθ_cont_uncurry.comp (by fun_prop)).continuousOn
  have hlft_cont : ContinuousOn (fun y => θ a y) (Set.Icc s t) := by
    have : (fun y => θ a y) = (Function.uncurry θ) ∘ (fun y : ℝ => (a, y)) := by
      funext y; simp [Function.uncurry]
    rw [this]; exact (hθ_cont_uncurry.comp (by fun_prop)).continuousOn
  -- The four edge sign conditions.
  have ha_mem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hb_mem : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  have hs_mem : s ∈ Set.Icc s t := Set.left_mem_Icc.mpr hst
  have ht_mem : t ∈ Set.Icc s t := Set.right_mem_Icc.mpr hst
  -- Bottom edge: `η = 1 > 0` ⟹ `exp · sin > 0` ⟹ `sin > 0`.
  have Hbot : ∀ x ∈ Set.Icc a b, 0 < Real.sin (θ x s) := by
    intro x hx
    have hηeq : η (Complex.mk x s) = 1 := by
      refine hηP _ (Set.mem_union_right _ ?_)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hmk_re]; exact hx.1
      · rw [hmk_re]; exact hx.2
      · rw [hmk_im]
    have := (hsign x hx s hs_mem).2
    rw [hηeq] at this
    have hexp_pos := Real.exp_pos ((L x s).re)
    nlinarith [this, hexp_pos, Real.exp_pos ((L x s).re)]
  -- Top edge: `η = -1 < 0` ⟹ `sin < 0`.
  have Htop : ∀ x ∈ Set.Icc a b, Real.sin (θ x t) < 0 := by
    intro x hx
    have hηeq : η (Complex.mk x t) = -1 := by
      refine hηQ _ (Set.mem_union_right _ ?_)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hmk_re]; exact hx.1
      · rw [hmk_re]; exact hx.2
      · rw [hmk_im]
    have := (hsign x hx t ht_mem).2
    rw [hηeq] at this
    have hexp_pos := Real.exp_pos ((L x t).re)
    nlinarith [this, hexp_pos]
  -- Right edge: `v = 1` ⟹ `v - c = 1 - c > 0` ⟹ `cos > 0`.
  have Hrgt : ∀ y ∈ Set.Icc s t, 0 < Real.cos (θ b y) := by
    intro y hy
    have hv1' : v (Complex.mk b y) = 1 := by
      refine hv1 _ ?_ ?_ ?_
      · rw [hmk_re]
      · rw [hmk_im]; exact hy.1
      · rw [hmk_im]; exact hy.2
    have hpos : 0 < v (Complex.mk b y) - c := by rw [hv1']; linarith [hc.2]
    have := (hsign b hb_mem y hy).1
    rw [this] at hpos
    have hexp_pos := Real.exp_pos ((L b y).re)
    nlinarith [hpos, hexp_pos]
  -- Left edge: `v = 0` ⟹ `v - c = -c < 0` ⟹ `cos < 0`.
  have Hlft : ∀ y ∈ Set.Icc s t, Real.cos (θ a y) < 0 := by
    intro y hy
    have hv0' : v (Complex.mk a y) = 0 := by
      refine hv0 _ ?_ ?_ ?_
      · rw [hmk_re]
      · rw [hmk_im]; exact hy.1
      · rw [hmk_im]; exact hy.2
    have hneg : v (Complex.mk a y) - c < 0 := by rw [hv0']; linarith [hc.1]
    have := (hsign a ha_mem y hy).1
    rw [this] at hneg
    have hexp_pos := Real.exp_pos ((L a y).re)
    nlinarith [hneg, hexp_pos]
  -- Conclude via the winding contradiction.
  exact square_crossing_contradiction hab hst θ hbot_cont hrgt_cont htop_cont hlft_cont
    Hbot Hrgt Htop Hlft

/-- **Level sets of a left-right transition function cross the rectangle bottom-to-top.**
For a continuous `v : ℂ → ℝ` with `v = 0` on the left edge and `v = 1` on the right edge of
the closed rectangle `[a,b] × [s,t]`, every intermediate level `c ∈ (0,1)` contains a
preconnected subset of the rectangle meeting both the bottom edge `{im = s}` and the top
edge `{im = t}`. This is the public, positive form of the plane-separation core
`rectLevel_no_split` (apply it by contradiction). -/
theorem exists_preconnected_level_crossing {a b s t : ℝ} (hab : a ≤ b) (hst : s ≤ t)
    {v : ℂ → ℝ} (hv : Continuous v)
    (hv0 : ∀ z : ℂ, z.re = a → s ≤ z.im → z.im ≤ t → v z = 0)
    (hv1 : ∀ z : ℂ, z.re = b → s ≤ z.im → z.im ≤ t → v z = 1)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ S : Set ℂ, IsPreconnected S ∧
      S ⊆ {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ (s ≤ z.im ∧ z.im ≤ t)} ∧
      (∀ z ∈ S, v z = c) ∧ (∃ p ∈ S, p.im = s) ∧ (∃ q ∈ S, q.im = t) := by
  by_contra hcon
  refine rectLevel_no_split hab hst hv hv0 hv1 hc ?_
  intro S hSpre hSsub hp hq
  rw [Set.subset_inter_iff] at hSsub
  refine hcon ⟨S, hSpre, hSsub.1, ?_, hp, hq⟩
  intro z hz
  have hzc := hSsub.2 hz
  rwa [Set.mem_preimage, Set.mem_singleton_iff] at hzc

/-! ### Arc-length Lipschitz reparametrization of a simple rectifiable arc

The decomposition of the rectifiable-continuum theorem `rectifiable_continuum_simple_arc` separates
its two ingredients:

* the **topological core** (Eilenberg–Harrold / Hahn–Mazurkiewicz, classically Mathlib-absent):
  a rectifiable continuum contains a *simple* (injective) **finite-variation** arc joining any
  two points — `simpleRectifiableArc_of_compact_connected_finite_hausdorff`; and
* the **arc-length reparametrization**: a simple finite-variation arc can be
  reparametrized to a globally Lipschitz simple arc on `[0,1]` — the genuine analytic content for
  which Mathlib does have machinery (`variationOnFromTo`, `Mathlib.Analysis.ConstantSpeed`).

The reparametrization uses the cumulative variation `S = variationOnFromTo γ [0,1] 0` as a
*continuous strictly monotone* bijection `[0,1] → [0, L]` (`L =` total length), reparametrizing by
its inverse so the new curve has constant speed `L`, hence is `L`-Lipschitz. -/

/-- Continuity of the cumulative variation `variationOnFromTo γ s a` on `s`, from continuity of the
curve `γ` (and bounded variation on `s`). This packages Mathlib's one-sided
`tendsto_eVariationOn_Icc_zero_left/right` into honest `ContinuousOn`. -/
theorem continuousOn_variationOnFromTo {γ : ℝ → ℂ} {s : Set ℝ}
    (hγ : Continuous γ) (hbv : BoundedVariationOn γ s) {a : ℝ} (ha : a ∈ s) :
    ContinuousOn (variationOnFromTo γ s a) s := by
  have hloc : LocallyBoundedVariationOn γ s := hbv.locallyBoundedVariationOn
  intro x hx
  have key : Filter.Tendsto (fun y => variationOnFromTo γ s x y) (𝓝[s] x) (𝓝 (0 : ℝ)) := by
    have hcL : ContinuousWithinAt γ (s ∩ Iic x) x := (hγ.continuousWithinAt).mono inter_subset_left
    have hcR : ContinuousWithinAt γ (s ∩ Ici x) x := (hγ.continuousWithinAt).mono inter_subset_left
    have hL := (BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left hbv hcL)
    have hR := (BoundedVariationOn.tendsto_eVariationOn_Icc_zero_right hbv x hcR)
    have hLr : Filter.Tendsto (fun y => (eVariationOn γ (s ∩ Icc y x)).toReal) (𝓝[s] x) (𝓝 0) := by
      have := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hL
      simpa using! this
    have hRr : Filter.Tendsto (fun y => (eVariationOn γ (s ∩ Icc x y)).toReal) (𝓝[s] x) (𝓝 0) := by
      have := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hR
      simpa using! this
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hLr.eventually (Metric.ball_mem_nhds 0 hε),
      hRr.eventually (Metric.ball_mem_nhds 0 hε)] with y hyL hyR
    rw [Real.dist_eq] at hyL hyR ⊢
    simp only [sub_zero] at hyL hyR ⊢
    rcases le_total y x with hyx | hxy
    · rw [variationOnFromTo.eq_of_ge γ s hyx, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]
      rw [abs_of_nonneg ENNReal.toReal_nonneg] at hyL
      exact hyL
    · rw [variationOnFromTo.eq_of_le γ s hxy, abs_of_nonneg ENNReal.toReal_nonneg]
      rw [abs_of_nonneg ENNReal.toReal_nonneg] at hyR
      exact hyR
  have hcongr : (fun y => variationOnFromTo γ s a y)
      =ᶠ[𝓝[s] x] (fun y => variationOnFromTo γ s a x + variationOnFromTo γ s x y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [variationOnFromTo.add hloc ha hx hy]
  rw [ContinuousWithinAt, Filter.tendsto_congr' hcongr]
  have heq : (𝓝 (variationOnFromTo γ s a x)) = 𝓝 (variationOnFromTo γ s a x + 0) := by rw [add_zero]
  rw [heq]
  exact tendsto_const_nhds.add key

/-- The clamp of a real number into `[0,1]`. Continuous, `1`-Lipschitz, fixes `[0,1]` pointwise,
and always lands in `[0,1]`; used to make the reparametrized arc *globally* Lipschitz. -/
noncomputable def clamp01 (τ : ℝ) : ℝ := max 0 (min 1 τ)

/-- `clamp01 τ` always lies in `[0, 1]`. -/
theorem clamp01_mem (τ : ℝ) : clamp01 τ ∈ Icc (0 : ℝ) 1 := by
  unfold clamp01
  refine ⟨le_max_left _ _, ?_⟩
  rcases le_total 1 τ with h | h
  · simp [h]
  · rw [min_eq_right h, max_le_iff]; exact ⟨by norm_num, h⟩

/-- `clamp01` fixes `[0, 1]` pointwise: `clamp01 τ = τ` for `τ ∈ [0, 1]`. -/
theorem clamp01_eq_self {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : clamp01 τ = τ := by
  unfold clamp01
  obtain ⟨h0, h1⟩ := hτ
  rw [min_eq_right h1, max_eq_right h0]

/-- `clamp01` is `1`-Lipschitz. -/
private theorem lipschitzWith_clamp01 : LipschitzWith 1 clamp01 := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro τ τ'
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  unfold clamp01
  have hmin : |min 1 τ - min 1 τ'| ≤ |τ - τ'| := by
    refine (abs_min_sub_min_le_max 1 τ 1 τ').trans ?_
    simp only [sub_self, abs_zero]
    exact max_le (abs_nonneg _) le_rfl
  refine (abs_max_sub_max_le_max 0 (min 1 τ) 0 (min 1 τ')).trans ?_
  simp only [sub_self, abs_zero]
  exact max_le (abs_nonneg _) hmin

/-- **Arc-length Lipschitz reparametrization** (the unconditional half of
`rectifiable_continuum_simple_arc`).

Given a continuous curve `γ` that is *injective* on `[0,1]` and of *finite total variation*
`eVariationOn γ [0,1] ≠ ∞`, there is a curve `δ` parametrized on `[0,1]` with the **same
endpoints**,
**globally Lipschitz** (hence continuous), **injective** on `[0,1]`, with trace inside `γ '' [0,1]`.

Reparametrize by cumulative arc length: `S t = variationOnFromTo γ [0,1] 0 t` is continuous
(`continuousOn_variationOnFromTo`) and *strictly* monotone (injectivity ⟹ positive variation over
each nondegenerate subinterval, via `eVariationOn.edist_le`), so it is a homeomorphism
`[0,1] ≃ [0, L]` with `L = (eVariationOn γ [0,1]).toReal > 0`. Composing `γ` with the (scaled,
clamped) inverse gives a constant-speed-`L` curve, which is `L`-Lipschitz by `eVariationOn.edist_le`
applied on subintervals. Clamping makes the Lipschitz bound global. -/
theorem lipschitz_simpleArc_of_finiteVariation {γ : ℝ → ℂ}
    (hγcont : Continuous γ) (hγinj : InjOn γ (Icc (0 : ℝ) 1))
    (hγbv : eVariationOn γ (Icc (0 : ℝ) 1) ≠ ∞) :
    ∃ δ : ℝ → ℂ, δ 0 = γ 0 ∧ δ 1 = γ 1 ∧ Continuous δ ∧
      (∃ K : ℝ≥0, LipschitzOnWith K δ (Set.uIcc 0 1)) ∧
      Set.InjOn δ (Set.Icc (0 : ℝ) 1) ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, δ τ ∈ γ '' (Icc (0 : ℝ) 1) := by
  set s : Set ℝ := Icc (0 : ℝ) 1 with hs
  have h0s : (0 : ℝ) ∈ s := by rw [hs]; constructor <;> norm_num
  have h1s : (1 : ℝ) ∈ s := by rw [hs]; constructor <;> norm_num
  have hbv : BoundedVariationOn γ s := hγbv
  have hloc : LocallyBoundedVariationOn γ s := hbv.locallyBoundedVariationOn
  set S : ℝ → ℝ := variationOnFromTo γ s 0 with hSdef
  set L : ℝ := (eVariationOn γ s).toReal with hLdef
  have hS0 : S 0 = 0 := by rw [hSdef]; exact variationOnFromTo.self γ s 0
  have hsIcc : s ∩ Icc (0 : ℝ) 1 = s := by rw [hs]; simp [Set.inter_self]
  have hS1 : S 1 = L := by
    rw [hSdef, hLdef, variationOnFromTo.eq_of_le γ s (by norm_num : (0 : ℝ) ≤ 1), hsIcc]
  have hSmono : MonotoneOn S s := variationOnFromTo.monotoneOn hloc h0s
  have hScont : ContinuousOn S s := continuousOn_variationOnFromTo hγcont hbv h0s
  -- strict mono: `S b < S c` for `b < c` in `s`, using injectivity ⟹ positive variation
  have hSstrict : ∀ b ∈ s, ∀ c ∈ s, b < c → S b < S c := by
    intro b hb c hc hbc
    have hadd : S b + variationOnFromTo γ s b c = S c := by
      rw [hSdef]; exact variationOnFromTo.add hloc h0s hb hc
    have hpos : 0 < variationOnFromTo γ s b c := by
      rw [variationOnFromTo.eq_of_le γ s hbc.le]
      have hbc' : b ∈ s ∩ Icc b c := ⟨hb, le_rfl, hbc.le⟩
      have hcc' : c ∈ s ∩ Icc b c := ⟨hc, hbc.le, le_rfl⟩
      have hne : γ b ≠ γ c := fun h => (hbc.ne) (hγinj hb hc h)
      have hedpos : 0 < edist (γ b) (γ c) := by rw [edist_pos]; exact hne
      have hsub : eVariationOn γ (s ∩ Icc b c) ≠ ∞ :=
        ne_top_of_le_ne_top hbv (eVariationOn.mono γ inter_subset_left)
      have hle : edist (γ b) (γ c) ≤ eVariationOn γ (s ∩ Icc b c) :=
        eVariationOn.edist_le γ hbc' hcc'
      have : (0 : ℝ≥0∞) < eVariationOn γ (s ∩ Icc b c) := lt_of_lt_of_le hedpos hle
      exact ENNReal.toReal_pos (ne_of_gt this) hsub
    linarith [hadd]
  have hLpos : 0 < L := by
    have := hSstrict 0 h0s 1 h1s (by norm_num)
    rw [hS0, hS1] at this; exact this
  have hLnn : 0 ≤ L := hLpos.le
  -- image of `S` is `Icc 0 L`
  have hSimage : S '' s = Icc 0 L := by
    have hcont' : ContinuousOn S (Icc (0 : ℝ) 1) := hScont
    have hmono' : MonotoneOn S (Icc (0 : ℝ) 1) := hSmono
    have himg := ContinuousOn.image_Icc_of_monotoneOn (a := (0 : ℝ)) (b := (1 : ℝ)) (f := S)
      (by norm_num) hcont' hmono'
    rw [hs, himg, hS0, hS1]
  -- the (generalized) inverse of `S` restricted to `s`
  set T : ℝ → ℝ := Function.invFunOn S s with hTdef
  have hTspec : ∀ v ∈ Icc (0 : ℝ) L, T v ∈ s ∧ S (T v) = v := by
    intro v hv
    have hex : ∃ a ∈ s, S a = v := by
      have : v ∈ S '' s := by rw [hSimage]; exact hv
      obtain ⟨a, ha, hav⟩ := this; exact ⟨a, ha, hav⟩
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  set δ : ℝ → ℂ := fun τ => γ (T (L * clamp01 τ)) with hδdef
  have hmulmem : ∀ τ, L * clamp01 τ ∈ Icc (0 : ℝ) L := by
    intro τ
    obtain ⟨hc0, hc1⟩ := clamp01_mem τ
    refine ⟨by positivity, ?_⟩
    nlinarith [hLnn]
  have hTmem : ∀ τ, T (L * clamp01 τ) ∈ s := fun τ => (hTspec _ (hmulmem τ)).1
  have hST : ∀ τ, S (T (L * clamp01 τ)) = L * clamp01 τ := fun τ => (hTspec _ (hmulmem τ)).2
  -- endpoints
  have hT0 : T 0 = 0 := by
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hLnn⟩
    have hm := (hTspec 0 h0mem).1
    have he := (hTspec 0 h0mem).2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hSstrict (T 0) hm 0 h0s h; rw [he, hS0] at this; exact lt_irrefl _ this
    · have := hSstrict 0 h0s (T 0) hm h; rw [he, hS0] at this; exact lt_irrefl _ this
  have hTL : T L = 1 := by
    have hLmem : L ∈ Icc (0 : ℝ) L := ⟨hLnn, le_rfl⟩
    have hm := (hTspec L hLmem).1
    have he := (hTspec L hLmem).2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hSstrict (T L) hm 1 h1s h; rw [he, hS1] at this; exact lt_irrefl _ this
    · have := hSstrict 1 h1s (T L) hm h; rw [he, hS1] at this; exact lt_irrefl _ this
  have hδ0 : δ 0 = γ 0 := by
    rw [hδdef]; simp only
    rw [show clamp01 0 = 0 from clamp01_eq_self (by constructor <;> norm_num), mul_zero, hT0]
  have hδ1 : δ 1 = γ 1 := by
    rw [hδdef]; simp only
    rw [show clamp01 1 = 1 from clamp01_eq_self (by constructor <;> norm_num), mul_one, hTL]
  -- global Lipschitz bound with constant `L`
  have hLip : LipschitzWith L.toNNReal δ := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro τ τ'
    set u := T (L * clamp01 τ) with hu
    set u' := T (L * clamp01 τ') with hu'
    have hus : u ∈ s := hTmem τ
    have hu's : u' ∈ s := hTmem τ'
    have hSu : S u = L * clamp01 τ := hST τ
    have hSu' : S u' = L * clamp01 τ' := hST τ'
    have hvar : variationOnFromTo γ s u u' = S u' - S u := by
      rw [hSdef]
      have := variationOnFromTo.add hloc h0s hus hu's
      linarith [this]
    have hdist_le : dist (γ u) (γ u') ≤ |S u' - S u| := by
      rw [dist_edist]
      have hmemuu : u ∈ s ∩ uIcc u u' := ⟨hus, left_mem_uIcc⟩
      have hmemuu' : u' ∈ s ∩ uIcc u u' := ⟨hu's, right_mem_uIcc⟩
      have hle : edist (γ u) (γ u') ≤ eVariationOn γ (s ∩ uIcc u u') :=
        eVariationOn.edist_le γ hmemuu hmemuu'
      have hsubne : eVariationOn γ (s ∩ uIcc u u') ≠ ∞ :=
        ne_top_of_le_ne_top hbv (eVariationOn.mono γ inter_subset_left)
      have hreal : (edist (γ u) (γ u')).toReal ≤ (eVariationOn γ (s ∩ uIcc u u')).toReal :=
        ENNReal.toReal_mono hsubne hle
      have hvareq : (eVariationOn γ (s ∩ uIcc u u')).toReal = |variationOnFromTo γ s u u'| := by
        rcases le_total u u' with h | h
        · rw [variationOnFromTo.eq_of_le γ s h, abs_of_nonneg ENNReal.toReal_nonneg, uIcc_of_le h]
        · rw [variationOnFromTo.eq_of_ge γ s h, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg,
            uIcc_of_ge h]
      rw [hvareq, hvar] at hreal
      exact hreal
    calc dist (δ τ) (δ τ') = dist (γ u) (γ u') := by rw [hδdef]
      _ ≤ |S u' - S u| := hdist_le
      _ = |L * clamp01 τ' - L * clamp01 τ| := by rw [hSu, hSu']
      _ = L * |clamp01 τ' - clamp01 τ| := by rw [← mul_sub, abs_mul, abs_of_nonneg hLnn]
      _ = L * dist (clamp01 τ') (clamp01 τ) := by rw [Real.dist_eq]
      _ ≤ L * dist τ' τ := by
            apply mul_le_mul_of_nonneg_left _ hLnn
            have := lipschitzWith_clamp01.dist_le_mul τ' τ; simpa using this
      _ = L * dist τ τ' := by rw [dist_comm]
      _ = (L.toNNReal : ℝ) * dist τ τ' := by rw [Real.coe_toNNReal L hLnn]
  refine ⟨δ, hδ0, hδ1, hLip.continuous,
    ⟨L.toNNReal, hLip.lipschitzOnWith.mono (subset_univ _)⟩, ?_, ?_⟩
  · -- injectivity on `[0,1]`
    intro τ hτ τ' hτ' heq
    rw [hδdef] at heq; simp only at heq
    have hinj := hγinj (hTmem τ) (hTmem τ') heq
    have hSeq : S (T (L * clamp01 τ)) = S (T (L * clamp01 τ')) := by rw [hinj]
    rw [hST, hST] at hSeq
    rw [clamp01_eq_self hτ, clamp01_eq_self hτ'] at hSeq
    exact mul_left_cancel₀ (ne_of_gt hLpos) hSeq
  · -- the trace lies in `γ '' [0,1]`
    intro τ hτ
    rw [hδdef]; simp only
    exact ⟨T (L * clamp01 τ), hTmem τ, rfl⟩

/-- **Constant-speed (arc-length) reparametrization of a continuous finite-variation path —
without assuming injectivity.**

Given any continuous curve `γ` of finite total variation on `[0,1]`, the cumulative-variation
reparametrization produces a curve `δ` on `[0,1]` with the **same endpoints**, **globally
`L`-Lipschitz** (`L =` total length), trace inside `γ '' [0,1]`, total variation `eVariationOn δ
[0,1] ≤ eVariationOn γ [0,1]`, and the crucial **constant-speed identity**

`variationOnFromTo δ [0,1] 0 τ = L * τ`  for `τ ∈ [0,1]`,

i.e. the cumulative variation of `δ` is exactly linear. This is the injectivity-free version of
`lipschitz_simpleArc_of_finiteVariation`; the constant-speed identity is what later forces a
length-*minimizing* `γ` to have an *injective* reparametrization (a positive arc-length gap forces a
positive-variation sub-loop, whose excision would shorten the path). -/
theorem constantSpeedReparam_of_finiteVariation {γ : ℝ → ℂ}
    (hγcont : Continuous γ) (hγbv : eVariationOn γ (Icc (0 : ℝ) 1) ≠ ∞) :
    ∃ δ : ℝ → ℂ, δ 0 = γ 0 ∧ δ 1 = γ 1 ∧ Continuous δ ∧
      LipschitzWith (eVariationOn γ (Icc (0 : ℝ) 1)).toReal.toNNReal δ ∧
      eVariationOn δ (Icc (0 : ℝ) 1) ≤ eVariationOn γ (Icc (0 : ℝ) 1) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, δ τ ∈ γ '' (Icc (0 : ℝ) 1)) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1,
        variationOnFromTo δ (Icc (0 : ℝ) 1) 0 τ
          = (eVariationOn γ (Icc (0 : ℝ) 1)).toReal * τ) := by
  set s : Set ℝ := Icc (0 : ℝ) 1 with hs
  have h0s : (0 : ℝ) ∈ s := by rw [hs]; constructor <;> norm_num
  have h1s : (1 : ℝ) ∈ s := by rw [hs]; constructor <;> norm_num
  have hbv : BoundedVariationOn γ s := hγbv
  have hloc : LocallyBoundedVariationOn γ s := hbv.locallyBoundedVariationOn
  set S : ℝ → ℝ := variationOnFromTo γ s 0 with hSdef
  set L : ℝ := (eVariationOn γ s).toReal with hLdef
  have hLnn : 0 ≤ L := ENNReal.toReal_nonneg
  have hS0 : S 0 = 0 := by rw [hSdef]; exact variationOnFromTo.self γ s 0
  have hsIcc : s ∩ Icc (0 : ℝ) 1 = s := by rw [hs]; simp [Set.inter_self]
  have hS1 : S 1 = L := by
    rw [hSdef, hLdef, variationOnFromTo.eq_of_le γ s (by norm_num : (0 : ℝ) ≤ 1), hsIcc]
  have hSmono : MonotoneOn S s := variationOnFromTo.monotoneOn hloc h0s
  have hScont : ContinuousOn S s := continuousOn_variationOnFromTo hγcont hbv h0s
  -- image of `S` is `Icc 0 L`
  have hSimage : S '' s = Icc 0 L := by
    have himg := ContinuousOn.image_Icc_of_monotoneOn (a := (0 : ℝ)) (b := (1 : ℝ)) (f := S)
      (by norm_num) hScont hSmono
    rw [hs, himg, hS0, hS1]
  -- the (generalized) inverse of `S` restricted to `s`
  set T : ℝ → ℝ := Function.invFunOn S s with hTdef
  have hTspec : ∀ v ∈ Icc (0 : ℝ) L, T v ∈ s ∧ S (T v) = v := by
    intro v hv
    have hex : ∃ a ∈ s, S a = v := by
      have : v ∈ S '' s := by rw [hSimage]; exact hv
      obtain ⟨a, ha, hav⟩ := this; exact ⟨a, ha, hav⟩
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  set δ : ℝ → ℂ := fun τ => γ (T (L * clamp01 τ)) with hδdef
  have hmulmem : ∀ τ, L * clamp01 τ ∈ Icc (0 : ℝ) L := by
    intro τ
    obtain ⟨hc0, hc1⟩ := clamp01_mem τ
    refine ⟨by positivity, ?_⟩
    nlinarith [hLnn]
  have hTmem : ∀ τ, T (L * clamp01 τ) ∈ s := fun τ => (hTspec _ (hmulmem τ)).1
  have hST : ∀ τ, S (T (L * clamp01 τ)) = L * clamp01 τ := fun τ => (hTspec _ (hmulmem τ)).2
  -- endpoints (S is monotone; need `S (T 0) = 0` and `S (T L) = L`, plus reach `0` and `1`)
  have hT0eq : S (T 0) = 0 := by
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hLnn⟩
    exact (hTspec 0 h0mem).2
  have hTLeq : S (T L) = L := by
    have hLmem : L ∈ Icc (0 : ℝ) L := ⟨hLnn, le_rfl⟩
    exact (hTspec L hLmem).2
  -- `γ` agrees at points of equal cumulative variation `S`.
  have hγeq_of_Seq : ∀ a ∈ s, ∀ b ∈ s, S a = S b → γ a = γ b := by
    intro a ha b hb hab
    have h0 : variationOnFromTo γ s a b = 0 := by
      have hadd := variationOnFromTo.add hloc h0s ha hb
      simp only [← hSdef] at hadd
      linarith [hadd, hab]
    exact edist_eq_zero.mp (variationOnFromTo.edist_zero_of_eq_zero hloc ha hb h0)
  have hcl0 : L * clamp01 0 = 0 := by
    rw [show clamp01 0 = 0 from clamp01_eq_self (by constructor <;> norm_num), mul_zero]
  have hcl1 : L * clamp01 1 = L := by
    rw [show clamp01 1 = 1 from clamp01_eq_self (by constructor <;> norm_num), mul_one]
  have hδ0 : δ 0 = γ 0 := by
    change γ (T (L * clamp01 0)) = γ 0
    refine hγeq_of_Seq _ (hTmem 0) 0 h0s ?_
    rw [hcl0] at *
    rw [hT0eq, hS0]
  have hδ1 : δ 1 = γ 1 := by
    change γ (T (L * clamp01 1)) = γ 1
    refine hγeq_of_Seq _ (hTmem 1) 1 h1s ?_
    rw [hcl1] at *
    rw [hTLeq, hS1]
  -- global Lipschitz bound with constant `L` (same computation as the injective version)
  have hLip : LipschitzWith L.toNNReal δ := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro τ τ'
    set u := T (L * clamp01 τ) with hu
    set u' := T (L * clamp01 τ') with hu'
    have hus : u ∈ s := hTmem τ
    have hu's : u' ∈ s := hTmem τ'
    have hSu : S u = L * clamp01 τ := hST τ
    have hSu' : S u' = L * clamp01 τ' := hST τ'
    have hvar : variationOnFromTo γ s u u' = S u' - S u := by
      have hadd := variationOnFromTo.add hloc h0s hus hu's
      simp only [← hSdef] at hadd
      linarith [hadd]
    have hdist_le : dist (γ u) (γ u') ≤ |S u' - S u| := by
      rw [dist_edist]
      have hmemuu : u ∈ s ∩ uIcc u u' := ⟨hus, left_mem_uIcc⟩
      have hmemuu' : u' ∈ s ∩ uIcc u u' := ⟨hu's, right_mem_uIcc⟩
      have hle : edist (γ u) (γ u') ≤ eVariationOn γ (s ∩ uIcc u u') :=
        eVariationOn.edist_le γ hmemuu hmemuu'
      have hsubne : eVariationOn γ (s ∩ uIcc u u') ≠ ∞ :=
        ne_top_of_le_ne_top hbv (eVariationOn.mono γ inter_subset_left)
      have hreal : (edist (γ u) (γ u')).toReal ≤ (eVariationOn γ (s ∩ uIcc u u')).toReal :=
        ENNReal.toReal_mono hsubne hle
      have hvareq : (eVariationOn γ (s ∩ uIcc u u')).toReal = |variationOnFromTo γ s u u'| := by
        rcases le_total u u' with h | h
        · rw [variationOnFromTo.eq_of_le γ s h, abs_of_nonneg ENNReal.toReal_nonneg, uIcc_of_le h]
        · rw [variationOnFromTo.eq_of_ge γ s h, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg,
            uIcc_of_ge h]
      rw [hvareq, hvar] at hreal
      exact hreal
    calc dist (δ τ) (δ τ') = dist (γ u) (γ u') := by rw [hδdef]
      _ ≤ |S u' - S u| := hdist_le
      _ = |L * clamp01 τ' - L * clamp01 τ| := by rw [hSu, hSu']
      _ = L * |clamp01 τ' - clamp01 τ| := by rw [← mul_sub, abs_mul, abs_of_nonneg hLnn]
      _ = L * dist (clamp01 τ') (clamp01 τ) := by rw [Real.dist_eq]
      _ ≤ L * dist τ' τ := by
            apply mul_le_mul_of_nonneg_left _ hLnn
            have := lipschitzWith_clamp01.dist_le_mul τ' τ; simpa using this
      _ = L * dist τ τ' := by rw [dist_comm]
      _ = (L.toNNReal : ℝ) * dist τ τ' := by rw [Real.coe_toNNReal L hLnn]
  -- trace inside `γ '' [0,1]`
  have htrace : ∀ τ ∈ Icc (0 : ℝ) 1, δ τ ∈ γ '' (Icc (0 : ℝ) 1) := by
    intro τ hτ
    exact ⟨T (L * clamp01 τ), hTmem τ, rfl⟩
  -- variation bound: `eVariationOn δ ≤ eVariationOn γ`, since `δ = γ ∘ (T ∘ (L • clamp01))` and the
  -- reparam `T ∘ (L • clamp01)` maps `[0,1]` monotonically into `s`.
  have hreparmono : MonotoneOn (fun τ => T (L * clamp01 τ)) (Icc (0 : ℝ) 1) := by
    intro τ hτ τ' hτ' hττ'
    -- `S` is monotone and injective-up-to-γ; use that `S (T v) = v` to compare `T v` values
    have hSv : S (T (L * clamp01 τ)) = L * clamp01 τ := hST τ
    have hSv' : S (T (L * clamp01 τ')) = L * clamp01 τ' := hST τ'
    have hclamp : clamp01 τ ≤ clamp01 τ' := by
      have := lipschitzWith_clamp01.dist_le_mul τ τ'
      -- clamp01 is monotone on ℝ
      unfold clamp01
      exact max_le_max le_rfl (min_le_min le_rfl hττ')
    have hvle : L * clamp01 τ ≤ L * clamp01 τ' := by nlinarith [hLnn]
    by_contra hlt
    push Not at hlt
    have hmono := hSmono (hTmem τ') (hTmem τ) hlt.le
    rw [hSv, hSv'] at hmono
    -- `L * clamp01 τ' ≤ L * clamp01 τ` and `L * clamp01 τ ≤ L * clamp01 τ'` ⟹ equal ⟹ `T` equal
    have heqv : L * clamp01 τ = L * clamp01 τ' := le_antisymm hvle hmono
    exact absurd (congrArg T heqv) (ne_of_gt hlt)
  have hvarle : eVariationOn δ s ≤ eVariationOn γ s := by
    have hmaps : MapsTo (fun τ => T (L * clamp01 τ)) s s := fun τ _ => hTmem τ
    have := eVariationOn.comp_le_of_monotoneOn γ (s := s) (t := s)
      (fun τ => T (L * clamp01 τ)) (hs ▸ hreparmono) hmaps
    simpa [hδdef, Function.comp] using! this
  -- constant-speed identity: `variationOnFromTo δ s 0 τ = L * τ` for `τ ∈ [0,1]`.
  -- On `s = [0,1]`, `δ = δ₀ ∘ φ` where `δ₀ = naturalParameterization γ s 0` has *unit* speed on
  -- `S '' s = Icc 0 L`, and `φ τ = L * τ` is the affine scaling onto `Icc 0 L`.
  set δ₀ : ℝ → ℂ := naturalParameterization γ s 0 with hδ₀def
  have hδ₀eq : ∀ v, δ₀ v = γ (T v) := fun v => by
    simp only [hδ₀def, naturalParameterization, Function.comp_apply, hTdef, hSdef]
  have hunit : HasUnitSpeedOn δ₀ (S '' s) := by
    have := has_unit_speed_naturalParameterization γ hloc h0s
    simpa only [hδ₀def, hSdef] using this
  rw [hSimage] at hunit
  -- `φ τ = L * τ`; on `s`, `δ τ = δ₀ (φ τ)`.
  set φ : ℝ → ℝ := fun τ => L * τ with hφdef
  have hδφ : ∀ τ ∈ s, δ τ = δ₀ (φ τ) := by
    intro τ hτ
    rw [hδ₀eq, hδdef]; simp only
    rw [clamp01_eq_self (by rw [← hs]; exact hτ)]
  have hφmono : MonotoneOn φ s := fun x _ y _ hxy => by
    simp only [hφdef]; exact mul_le_mul_of_nonneg_left hxy hLnn
  have hφimage : φ '' s = Icc 0 L := by
    rw [hs]; ext v; simp only [hφdef, mem_image, mem_Icc]
    constructor
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩; exact ⟨by positivity, by nlinarith [hLnn]⟩
    · rintro ⟨hv0, hvL⟩
      rcases eq_or_lt_of_le hLnn with hL0 | hLpos
      · refine ⟨0, ⟨le_rfl, by norm_num⟩, ?_⟩
        have : v = 0 := le_antisymm (hvL.trans hL0.symm.le) hv0
        rw [this, mul_zero]
      · refine ⟨v / L, ⟨by positivity, by rw [div_le_one hLpos]; exact hvL⟩, ?_⟩
        field_simp
  -- constant speed `L` of `δ` on `s`, via composition of unit-speed `δ₀` with the scaling `φ`.
  have hspeedConst : ∀ x ∈ s, ∀ y ∈ s, x ≤ y →
      eVariationOn δ (s ∩ Icc x y) = ENNReal.ofReal (L * (y - x)) := by
    intro x hx y hy hxy
    have hcongr : eVariationOn δ (s ∩ Icc x y) = eVariationOn (δ₀ ∘ φ) (s ∩ Icc x y) := by
      apply eVariationOn.congr
      intro τ hτ; exact hδφ τ hτ.1
    rw [hcongr, eVariationOn.comp_inter_Icc_eq_of_monotoneOn δ₀ φ hφmono hx hy, hφimage]
    -- `δ₀` unit speed on `Icc 0 L`:
    -- `eVariationOn δ₀ (Icc 0 L ∩ Icc (φ x)(φ y)) = ofReal(φ y - φ x)`
    have hφx : φ x ∈ Icc (0 : ℝ) L := by rw [← hφimage]; exact ⟨x, hx, rfl⟩
    have hφy : φ y ∈ Icc (0 : ℝ) L := by rw [← hφimage]; exact ⟨y, hy, rfl⟩
    have := hunit hφx hφy
    simp only [NNReal.coe_one, one_mul] at this
    rw [this]
    congr 1
    simp only [hφdef]; ring
  -- package as `variationOnFromTo δ s 0 τ = L * τ`.
  have hδloc : LocallyBoundedVariationOn δ s := by
    have : HasConstantSpeedOnWith δ s L.toNNReal := by
      rw [hasConstantSpeedOnWith_iff_ordered]
      intro x hx y hy hxy
      rw [hspeedConst x hx y hy hxy]; congr 1; simp [Real.coe_toNNReal L hLnn]
    exact this.hasLocallyBoundedVariationOn
  have hspeed : ∀ τ ∈ Icc (0 : ℝ) 1, variationOnFromTo δ s 0 τ = L * τ := by
    intro τ hτ
    have hτs : τ ∈ s := hτ
    rw [variationOnFromTo.eq_of_le δ s hτ.1, hspeedConst 0 h0s τ hτs hτ.1]
    rw [ENNReal.toReal_ofReal (by nlinarith [hLnn, hτ.1] : 0 ≤ L * (τ - 0))]
    ring
  exact ⟨δ, hδ0, hδ1, hLip.continuous, hLip, hvarle, htrace, hspeed⟩

/-- **A connected continuum's diameter is bounded by its `μH[1]`-length.**

For a (pre)connected subset `Γ ⊆ ℂ`, the Euclidean diameter is at most the one-dimensional Hausdorff
measure: `diam Γ ≤ μH[1] Γ`. The proof is the classical projection argument: for any two points
`p, q ∈ Γ`, project `Γ` orthogonally onto the real line through the direction `p - q` via a
`1`-Lipschitz `ℝ`-linear map `π : ℂ → ℝ`. Then `μH[1] (π '' Γ) ≤ μH[1] Γ`
(`LipschitzWith.hausdorffMeasure_image_le`), and `π '' Γ` is connected (continuous image of a
connected set) hence order-connected in `ℝ`, so it contains the whole interval between `π p` and
`π q`; therefore `μH[1] Γ ≥ μH[1] (π '' Γ) ≥ |π p − π q| = ‖p − q‖` for the chosen direction. Taking
the supremum over `p, q` gives `diam Γ ≤ μH[1] Γ` in the `ℝ≥0∞` (extended) sense `ediam`. -/
theorem ediam_le_hausdorffMeasure_one_of_isPreconnected {Γ : Set ℂ} (hΓ : IsPreconnected Γ) :
    Metric.ediam Γ ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ := by
  -- It suffices to bound `edist x y` by `μH[1] Γ` for all `x, y ∈ Γ`.
  apply Metric.ediam_le
  intro x hx y hy
  set H : ℝ≥0∞ := (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ with hHdef
  -- Reduce to the real distance `d = ‖x - y‖`.
  set d : ℝ := ‖x - y‖ with hddef
  have hd0 : 0 ≤ d := norm_nonneg _
  have hedist : edist x y = ENNReal.ofReal d := by rw [edist_dist, dist_eq_norm]
  rw [hedist]
  rcases eq_or_lt_of_le hd0 with hd | hdpos
  · -- `d = 0`: trivial.
    rw [← hd, ENNReal.ofReal_zero]; exact zero_le
  · -- `d > 0`: project along `w = x - y` by the real inner product `pr z = ⟪z, w⟫_ℝ`.
    set w : ℂ := x - y with hwdef
    have hwnorm : ‖w‖ = d := rfl
    set pr : ℂ → ℝ := fun z => @inner ℝ ℂ _ z w with hprdef
    -- `pr` is `‖w‖`-Lipschitz.
    have hlip : LipschitzWith ‖w‖.toNNReal pr := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      rw [Real.dist_eq, hprdef]
      change |@inner ℝ ℂ _ a w - @inner ℝ ℂ _ b w| ≤ _
      rw [← inner_sub_left]
      calc |@inner ℝ ℂ _ (a - b) w| ≤ ‖a - b‖ * ‖w‖ := abs_real_inner_le_norm _ _
        _ = ‖w‖.toNNReal * dist a b := by
            rw [Real.coe_toNNReal _ (norm_nonneg _), dist_eq_norm]; ring
    -- the difference of projected endpoints is `d²`.
    have hdiff : pr x - pr y = d * d := by
      change @inner ℝ ℂ _ x w - @inner ℝ ℂ _ y w = d * d
      rw [← inner_sub_left, ← hwdef, ← hwnorm, ← real_inner_self_eq_norm_mul_norm w]
    have hyx : pr y ≤ pr x := by linarith [hdiff, mul_nonneg hd0 hd0]
    -- `pr '' Γ` is preconnected hence order-connected; contains the interval `[pr y, pr x]`.
    have hcontpr : Continuous pr := hlip.continuous
    have hsub : Set.Icc (pr y) (pr x) ⊆ pr '' Γ :=
      (hΓ.image pr hcontpr.continuousOn).ordConnected.out ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩
    -- `μH[1]([pr y, pr x]) = ofReal (pr x - pr y) = ofReal (d²)`.
    have hIcc : (μH[1] : Measure ℝ) (Set.Icc (pr y) (pr x)) = ENNReal.ofReal (d * d) := by
      rw [hausdorffMeasure_real, Real.volume_Icc, hdiff]
    -- lower bound on `μH[1] (pr '' Γ)`.
    have hlow : ENNReal.ofReal (d * d) ≤ (μH[1] : Measure ℝ) (pr '' Γ) := by
      rw [← hIcc]; exact measure_mono hsub
    -- upper bound on `μH[1] (pr '' Γ)`.
    have hup : (μH[1] : Measure ℝ) (pr '' Γ) ≤ ‖w‖.toNNReal * H := by
      have := hlip.hausdorffMeasure_image_le (zero_le_one) Γ
      simpa using this
    -- combine: `ofReal (d²) ≤ ofReal d * H`.
    have hcomb : ENNReal.ofReal (d * d) ≤ ENNReal.ofReal d * H := by
      refine hlow.trans (hup.trans ?_)
      rw [hwnorm, show (d.toNNReal : ℝ≥0∞) = ENNReal.ofReal d from rfl]
    -- cancel the positive finite factor `ofReal d`.
    have hofd0 : ENNReal.ofReal d ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr hdpos
    have hofdtop : ENNReal.ofReal d ≠ ∞ := ENNReal.ofReal_ne_top
    have hsq : ENNReal.ofReal (d * d) = ENNReal.ofReal d * ENNReal.ofReal d :=
      ENNReal.ofReal_mul hd0
    rw [hsq] at hcomb
    exact (ENNReal.mul_le_mul_iff_right hofd0 hofdtop).mp hcomb

/-- **Localized continuum length lower bound (the per-ball packing estimate).**

For a connected set `Γ ⊆ ℂ`, a center `z ∈ Γ`, a radius `r > 0`, and a point `w ∈ Γ` with
`r ≤ dist z w`, the local `μH[1]`-length inside the closed ball of radius `r` about `z` is at least
`r`:
`ofReal r ≤ μH[1] (Γ ∩ closedBall z r)`.

The proof is the *localized* projection argument that **avoids any boundary-bumping / sub-continuum
construction**. Consider the `1`-Lipschitz "clamped distance" `f x = min (dist z x) r`. It is
constant `= r` outside the open ball, so `f '' Γ = f '' (Γ ∩ closedBall z r)` away from the single
value `r`; on `Γ ∩ closedBall z r` one has `f x = dist z x`. The continuous image `f '' Γ` is
connected, contains `f z = 0` and `f w = r` (since `r ≤ dist z w`), hence by the intermediate value
theorem contains the whole interval `[0, r]`, and `[0, r) ⊆ f '' (Γ ∩ closedBall z r)`. Therefore
`μH[1] (Γ ∩ closedBall z r) ≥ μH[1] (f '' (Γ ∩ closedBall z r)) ≥ μH[1] [0, r) = r`, using that the
`1`-Lipschitz `f` does not increase `μH[1]` (`LipschitzWith.hausdorffMeasure_image_le`) and
`hausdorffMeasure_real`. -/
theorem ofReal_le_hausdorffMeasure_one_inter_closedBall {Γ : Set ℂ} (hΓconn : IsConnected Γ)
    {z : ℂ} (hz : z ∈ Γ) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ Γ) (hrw : r ≤ dist z w) :
    ENNReal.ofReal r ≤
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (Γ ∩ Metric.closedBall z r) := by
  classical
  -- The clamped distance `f x = min (dist z x) r`, `1`-Lipschitz.
  set f : ℂ → ℝ := fun x => min (dist z x) r with hfdef
  have hflip : LipschitzWith 1 f := (LipschitzWith.dist_right z).min_const r
  have hfcont : Continuous f := hflip.continuous
  -- `f z = 0` and `f w = r`.
  have hfz : f z = 0 := by simp [hfdef, dist_self, le_of_lt hr]
  have hfw : f w = r := by simp [hfdef, min_eq_right hrw]
  -- `[0, r] ⊆ f '' Γ` by the intermediate value theorem on the connected `Γ`.
  have hIVT : Set.Icc (0 : ℝ) r ⊆ f '' Γ := by
    have h := hΓconn.isPreconnected.intermediate_value hz hw hfcont.continuousOn
    rwa [hfz, hfw] at h
  -- `f '' (Γ ∩ closedBall z r)` contains `[0, r)`.
  set B : Set ℂ := Γ ∩ Metric.closedBall z r with hBdef
  have hcover : Set.Ico (0 : ℝ) r ⊆ f '' B := by
    intro t ht
    obtain ⟨ht0, htr⟩ := ht
    obtain ⟨x, hxΓ, hfx⟩ := hIVT ⟨ht0, le_of_lt htr⟩
    -- `f x = t < r` forces `min (dist z x) r = t`, so `dist z x = t ≤ r`, i.e. `x ∈ closedBall`.
    have hdzx : dist z x = t := by
      have : min (dist z x) r = t := hfx
      rcases le_or_gt (dist z x) r with hle | hlt
      · rwa [min_eq_left hle] at this
      · rw [min_eq_right (le_of_lt hlt)] at this; exact absurd this.symm (ne_of_lt htr)
    refine ⟨x, ⟨hxΓ, ?_⟩, hfx⟩
    rw [Metric.mem_closedBall, dist_comm]; rw [hdzx]; exact le_of_lt htr
  -- length lower bound: `r = μH[1] [0, r) ≤ μH[1] (f '' B) ≤ μH[1] B`.
  have h1 : (μH[1] : Measure ℝ) (Set.Ico (0 : ℝ) r) = ENNReal.ofReal r := by
    rw [hausdorffMeasure_real, Real.volume_Ico, sub_zero]
  have h2 : (μH[1] : Measure ℝ) (Set.Ico (0 : ℝ) r) ≤ (μH[1] : Measure ℝ) (f '' B) :=
    measure_mono hcover
  have h3 : (μH[1] : Measure ℝ) (f '' B) ≤
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) B := by
    have := hflip.hausdorffMeasure_image_le (zero_le_one) B
    simpa using this
  calc ENNReal.ofReal r = (μH[1] : Measure ℝ) (Set.Ico (0 : ℝ) r) := h1.symm
    _ ≤ (μH[1] : Measure ℝ) (f '' B) := h2
    _ ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) B := h3

/-- **Far-point existence in a set of diameter `> 2r`.** If `z ∈ Γ` and
`ofReal (2 * r) < ediam Γ`, there is `w ∈ Γ` with `r ≤ dist z w`. Indeed the strict diameter excess
provides a pair `a, b ∈ Γ` with `2r < dist a b ≤ dist a z + dist z b`, so one of `dist z a`,
`dist z b` is `> r`. -/
theorem exists_far_point_of_lt_ediam {Γ : Set ℂ} {z : ℂ} {r : ℝ}
    (hdiam : ENNReal.ofReal (2 * r) < Metric.ediam Γ) :
    ∃ w ∈ Γ, r ≤ dist z w := by
  -- The strict bound `ofReal (2r) < ediam Γ` yields a pair `a, b ∈ Γ`
  -- with `ofReal (2r) < edist a b`.
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ Γ, ∃ b ∈ Γ, ENNReal.ofReal (2 * r) < edist a b := by
    by_contra hcon
    push Not at hcon
    exact absurd (Metric.ediam_le (fun a ha b hb => hcon a ha b hb)) (not_le.mpr hdiam)
  -- Translate to real distances: `2r < dist a b ≤ dist a z + dist z b`.
  have hdab : 2 * r < dist a b := by
    have hd : edist a b = ENNReal.ofReal (dist a b) := by rw [edist_dist]
    rw [hd] at hab
    by_contra hcon
    push Not at hcon
    exact absurd hab (not_lt.mpr (ENNReal.ofReal_le_ofReal hcon))
  have htri : dist a b ≤ dist a z + dist z b := dist_triangle a z b
  -- One of the legs is `≥ r`.
  rcases le_or_gt r (dist z a) with hza | hza
  · exact ⟨a, ha, hza⟩
  · refine ⟨b, hb, ?_⟩
    have hza' : dist a z < r := by rw [dist_comm]; exact hza
    linarith

/-- **The packing bound (lower-content estimate).**

Let `Γ ⊆ ℂ` be connected with `ofReal ε < ediam Γ` (`ε > 0`), and let `C` be a **finite**
`ε`-separated subset of `Γ` (distinct centers more than `ε` apart). The closed balls
`closedBall z (ε/2)` for `z ∈ C` are pairwise disjoint, and each captures local `μH[1]`-length
`≥ ε/2` (by `ofReal_le_hausdorffMeasure_one_inter_closedBall`, since the strict diameter excess
`ofReal ε < ediam Γ` provides for every center a point of `Γ` at distance `≥ ε/2`). Summing the
disjoint contributions gives `#C · (ε/2) ≤ μH[1] Γ`.

This is the genuinely two-dimensional, classically Mathlib-absent **lower-content / packing**
estimate at the heart of the Eilenberg–Harrold ε-chain length bound — obtained here from the
localized continuum length estimate, with no boundary-bumping. -/
theorem packing_card_mul_le_hausdorffMeasure_one {Γ : Set ℂ} (hΓconn : IsConnected Γ)
    (hΓmeas : MeasurableSet Γ) {ε : ℝ} (hε : 0 < ε) (hdiam : ENNReal.ofReal ε < Metric.ediam Γ)
    {C : Finset ℂ} (hCΓ : ↑C ⊆ Γ) (hCsep : ∀ z ∈ C, ∀ w ∈ C, z ≠ w → ε < dist z w) :
    (C.card : ℝ≥0∞) * ENNReal.ofReal (ε / 2) ≤
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ := by
  classical
  set r : ℝ := ε / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; positivity
  -- The disjoint closed balls indexed by `C`.
  set B : ℂ → Set ℂ := fun z => Γ ∩ Metric.closedBall z r with hBdef
  -- Pairwise disjoint.
  have hdisj : (↑C : Set ℂ).PairwiseDisjoint B := by
    intro z hz w hw hzw
    have hsep : ε < dist z w := hCsep z hz w hw hzw
    have hball : Disjoint (Metric.closedBall z r) (Metric.closedBall w r) := by
      apply Metric.closedBall_disjoint_closedBall
      rw [hrdef]; linarith
    exact (hball.mono inter_subset_right inter_subset_right)
  -- Each ball is measurable.
  have hmeas : ∀ z ∈ C, MeasurableSet (B z) := fun z _ =>
    hΓmeas.inter measurableSet_closedBall
  -- Per-ball lower bound `ofReal r ≤ μH[1] (B z)`.
  have hperball : ∀ z ∈ C, ENNReal.ofReal r ≤
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (B z) := by
    intro z hz
    have hzΓ : z ∈ Γ := hCΓ hz
    -- far point: `ofReal (2r) = ofReal ε < ediam Γ`.
    have h2r : ENNReal.ofReal (2 * r) = ENNReal.ofReal ε := by rw [hrdef]; ring_nf
    have hfar : ENNReal.ofReal (2 * r) < Metric.ediam Γ := by rw [h2r]; exact hdiam
    obtain ⟨w, hwΓ, hrw⟩ := exists_far_point_of_lt_ediam (z := z) (r := r) hfar
    exact ofReal_le_hausdorffMeasure_one_inter_closedBall hΓconn hzΓ hr hwΓ hrw
  -- Disjoint additivity: `∑ μH[1] (B z) = μH[1] (⋃ B z) ≤ μH[1] Γ`.
  have hsum : ∑ z ∈ C, (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (B z) =
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (⋃ z ∈ C, B z) :=
    (measure_biUnion_finset hdisj hmeas).symm
  have hunionsub : (⋃ z ∈ C, B z) ⊆ Γ := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨z, _, hxz⟩ := hx
    exact hxz.1
  -- Assemble: `card · ofReal r ≤ ∑ μH[1] (B z) = μH[1] (⋃) ≤ μH[1] Γ`.
  calc (C.card : ℝ≥0∞) * ENNReal.ofReal (ε / 2)
      = ∑ _z ∈ C, ENNReal.ofReal r := by
        rw [Finset.sum_const, nsmul_eq_mul, hrdef]
    _ ≤ ∑ z ∈ C, (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (B z) :=
        Finset.sum_le_sum hperball
    _ = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (⋃ z ∈ C, B z) := hsum
    _ ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ := measure_mono hunionsub


end RhoPotentialWitness

end NoWanderingDomains
