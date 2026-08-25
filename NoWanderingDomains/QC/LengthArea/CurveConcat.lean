/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.LengthArea.CurveModulus

/-!
# Concatenation of absolutely continuous curves

The ρ-length distance obtained from `arcLengthLineIntegral` satisfies a triangle inequality: if a
curve joins `a` to `b` and another joins `b` to `c`, their concatenation joins `a` to `c` and its
arc-length line integral is the sum of the two. This file builds that concatenation.

Given two curves `γ₁, γ₂ : ℝ → ℂ` on `[0, 1]` with `γ₁ 1 = γ₂ 0`, the concatenation
`γ t = if t ≤ 1/2 then γ₁ (2 t) else γ₂ (2 t - 1)` traverses `γ₁` on `[0, 1/2]` and `γ₂` on
`[1/2, 1]`. When `γ₁` and `γ₂` are continuous and absolutely continuous on `[0, 1]`, so is `γ`, and
for every density `ρ`,

`arcLengthLineIntegral ρ γ = arcLengthLineIntegral ρ γ₁ + arcLengthLineIntegral ρ γ₂`.

## Main results

* `NoWanderingDomains.exists_concat_curve` — existence of the concatenated curve with matching
  endpoints, image contained in the union of the two images, and additivity of the arc-length line
  integral.

Two absolute-continuity primitives are proved on the way and are reusable:

* `AbsolutelyContinuousOnInterval.union_of_split` — gluing absolute continuity across two adjacent
  intervals `[a, c]` and `[c, b]`;
* `AbsolutelyContinuousOnInterval.comp_affine` — absolute continuity of an affine
  reparametrization `t ↦ η (m t + k)` (with `m > 0`) of an absolutely continuous curve.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **Absolute continuity glues across adjacent intervals.** If `f` is absolutely continuous on
`[a, c]` and on `[c, b]` with `a ≤ c ≤ b`, then it is absolutely continuous on `[a, b]`. A partition
of `[a, b]` of small total length is split at `c`: clamping each subinterval to `[a, c]` and to
`[c, b]` produces two admissible partitions, and the triangle inequality through `f c` bounds each
distance by the sum of the two clamped distances. -/
theorem AbsolutelyContinuousOnInterval.union_of_split {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (h1 : AbsolutelyContinuousOnInterval f a c) (h2 : AbsolutelyContinuousOnInterval f c b) :
    AbsolutelyContinuousOnInterval f a b := by
  have hab : a ≤ b := hac.trans hcb
  -- Triangle inequality through `f c` on a single subinterval `[x, y]`.
  have tri_split : ∀ (x y : ℝ),
      dist (f x) (f y)
        ≤ dist (f (min x c)) (f (min y c)) + dist (f (max x c)) (f (max y c)) := by
    intro x y
    rcases le_total x y with hxy | hyx
    · rcases le_total y c with hyc | hcy
      · rw [min_eq_left (hxy.trans hyc), min_eq_left hyc, max_eq_right (hxy.trans hyc),
          max_eq_right hyc, dist_self, add_zero]
      · rcases le_total x c with hxc | hcx
        · rw [min_eq_left hxc, min_eq_right hcy, max_eq_right hxc, max_eq_left hcy]
          exact dist_triangle _ _ _
        · rw [min_eq_right hcx, min_eq_right (hcx.trans hxy), max_eq_left hcx,
            max_eq_left (hcx.trans hxy), dist_self, zero_add]
    · rw [dist_comm (f x) (f y), dist_comm (f (min x c)) (f (min y c)),
        dist_comm (f (max x c)) (f (max y c))]
      rcases le_total x c with hxc | hcx
      · rw [min_eq_left hxc, min_eq_left (hyx.trans hxc), max_eq_right hxc,
          max_eq_right (hyx.trans hxc), dist_self, add_zero]
      · rcases le_total y c with hyc | hcy
        · rw [min_eq_right hcx, min_eq_left hyc, max_eq_left hcx, max_eq_right hyc]
          exact dist_triangle _ _ _
        · rw [min_eq_right hcx, min_eq_right hcy, max_eq_left hcx, max_eq_left hcy,
            dist_self, zero_add]
  -- Clamping to `[·, c]` keeps the open interval inside the original.
  have uIoc_min : ∀ (x y : ℝ), Set.uIoc (min x c) (min y c) ⊆ Set.uIoc x y := by
    intro x y z hz
    rw [Set.mem_uIoc] at hz ⊢
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨?_, h2.trans (min_le_left _ _)⟩
      rcases le_or_gt x c with h | h
      · rwa [min_eq_left h] at h1
      · rw [min_eq_right h.le] at h1; linarith [h2.trans (min_le_right y c)]
    · refine Or.inr ⟨?_, h2.trans (min_le_left _ _)⟩
      rcases le_or_gt y c with h | h
      · rwa [min_eq_left h] at h1
      · rw [min_eq_right h.le] at h1; linarith [h2.trans (min_le_right x c)]
  have uIoc_max : ∀ (x y : ℝ), Set.uIoc (max x c) (max y c) ⊆ Set.uIoc x y := by
    intro x y z hz
    rw [Set.mem_uIoc] at hz ⊢
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨lt_of_le_of_lt (le_max_left _ _) h1, ?_⟩
      rcases le_or_gt c y with h | h
      · rwa [max_eq_left h] at h2
      · rw [max_eq_right h.le] at h2; linarith [lt_of_le_of_lt (le_max_right x c) h1]
    · refine Or.inr ⟨lt_of_le_of_lt (le_max_left _ _) h1, ?_⟩
      rcases le_or_gt c x with h | h
      · rwa [max_eq_left h] at h2
      · rw [max_eq_right h.le] at h2; linarith [lt_of_le_of_lt (le_max_right y c) h1]
  rw [absolutelyContinuousOnInterval_iff] at h1 h2 ⊢
  intro ε hε
  obtain ⟨δ1, hδ1, hb1⟩ := h1 (ε / 2) (by positivity)
  obtain ⟨δ2, hδ2, hb2⟩ := h2 (ε / 2) (by positivity)
  refine ⟨min δ1 δ2, by positivity, ?_⟩
  rintro ⟨n, I⟩ hmem hlen
  simp only [AbsolutelyContinuousOnInterval.disjWithin, Finset.mem_range, mem_ofPred_eq] at hmem
  obtain ⟨hmemIcc, hdisj⟩ := hmem
  set Il : ℕ → ℝ × ℝ := fun i => (min (I i).1 c, min (I i).2 c) with hIl
  set Ir : ℕ → ℝ × ℝ := fun i => (max (I i).1 c, max (I i).2 c) with hIr
  have hlen_le_min : ∀ i, dist (Il i).1 (Il i).2 ≤ dist (I i).1 (I i).2 := fun i => by
    simpa [hIl] using (LipschitzWith.min_const (LipschitzWith.id) c).dist_le_mul (I i).1 (I i).2
  have hlen_le_max : ∀ i, dist (Ir i).1 (Ir i).2 ≤ dist (I i).1 (I i).2 := fun i => by
    simpa [hIr] using (LipschitzWith.max_const (LipschitzWith.id) c).dist_le_mul (I i).1 (I i).2
  have hmemL : (n, Il) ∈ AbsolutelyContinuousOnInterval.disjWithin a c := by
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨hx, hy⟩ := hmemIcc i (Finset.mem_range.mp hi)
      rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx hy
      rw [Set.uIcc_of_le hac]
      refine ⟨?_, ?_⟩
      · simp only [hIl, Set.mem_Icc]; exact ⟨le_min hx.1 hac, min_le_right _ _⟩
      · simp only [hIl, Set.mem_Icc]; exact ⟨le_min hy.1 hac, min_le_right _ _⟩
    · intro i hi j hj hij
      exact (hdisj hi hj hij).mono (uIoc_min _ _) (uIoc_min _ _)
  have hmemR : (n, Ir) ∈ AbsolutelyContinuousOnInterval.disjWithin c b := by
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨hx, hy⟩ := hmemIcc i (Finset.mem_range.mp hi)
      rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx hy
      rw [Set.uIcc_of_le hcb]
      refine ⟨?_, ?_⟩
      · simp only [hIr, Set.mem_Icc]; exact ⟨le_max_right _ _, max_le hx.2 hcb⟩
      · simp only [hIr, Set.mem_Icc]; exact ⟨le_max_right _ _, max_le hy.2 hcb⟩
    · intro i hi j hj hij
      exact (hdisj hi hj hij).mono (uIoc_max _ _) (uIoc_max _ _)
  have hlenL : ∑ i ∈ Finset.range n, dist (Il i).1 (Il i).2 < δ1 :=
    lt_of_le_of_lt (Finset.sum_le_sum (fun i _ => hlen_le_min i))
      (lt_of_lt_of_le hlen (min_le_left _ _))
  have hlenR : ∑ i ∈ Finset.range n, dist (Ir i).1 (Ir i).2 < δ2 :=
    lt_of_le_of_lt (Finset.sum_le_sum (fun i _ => hlen_le_max i))
      (lt_of_lt_of_le hlen (min_le_right _ _))
  have hsumL := hb1 (n, Il) hmemL hlenL
  have hsumR := hb2 (n, Ir) hmemR hlenR
  calc ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2)
      ≤ ∑ i ∈ Finset.range n,
          (dist (f (Il i).1) (f (Il i).2) + dist (f (Ir i).1) (f (Ir i).2)) :=
        Finset.sum_le_sum (fun i _ => tri_split (I i).1 (I i).2)
    _ = (∑ i ∈ Finset.range n, dist (f (Il i).1) (f (Il i).2))
          + ∑ i ∈ Finset.range n, dist (f (Ir i).1) (f (Ir i).2) := Finset.sum_add_distrib
    _ < ε / 2 + ε / 2 := add_lt_add hsumL hsumR
    _ = ε := by ring

/-- **Absolute continuity is preserved under an increasing affine reparametrization.** If `η` is
absolutely continuous on `[c, d]` and `t ↦ m t + k` (with `m > 0`) maps `[a, b]` into `[c, d]`, then
`t ↦ η (m t + k)` is absolutely continuous on `[a, b]`. The affine map sends an admissible partition
of `[a, b]` to an admissible partition of `[c, d]`, scaling total lengths by `m`. -/
theorem AbsolutelyContinuousOnInterval.comp_affine {X : Type*} [PseudoMetricSpace X] {η : ℝ → X}
    {m k a b c d : ℝ} (hm : 0 < m) (hη : AbsolutelyContinuousOnInterval η c d)
    (hmaps : ∀ t ∈ Set.uIcc a b, m * t + k ∈ Set.uIcc c d) :
    AbsolutelyContinuousOnInterval (fun t => η (m * t + k)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hη ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hη ε hε
  refine ⟨δ / m, by positivity, fun E hE hlen => ?_⟩
  set F : ℕ → ℝ × ℝ := fun i => (m * (E.2 i).1 + k, m * (E.2 i).2 + k) with hF
  have hdistF : ∀ i, dist (F i).1 (F i).2 = m * dist (E.2 i).1 (E.2 i).2 := by
    intro i
    simp only [hF, Real.dist_eq]
    rw [show m * (E.2 i).1 + k - (m * (E.2 i).2 + k) = m * ((E.2 i).1 - (E.2 i).2) from by ring,
      abs_mul, abs_of_pos hm]
  simp only [AbsolutelyContinuousOnInterval.disjWithin, Finset.mem_range, mem_ofPred_eq] at hE
  obtain ⟨hEicc, hEdisj⟩ := hE
  have hmemF : (E.1, F) ∈ AbsolutelyContinuousOnInterval.disjWithin c d := by
    refine ⟨fun i hi => ?_, ?_⟩
    · simp only [hF]
      exact ⟨hmaps _ (hEicc i (Finset.mem_range.mp hi)).1,
        hmaps _ (hEicc i (Finset.mem_range.mp hi)).2⟩
    · intro i hi j hj hij
      have hsub : ∀ x y : ℝ,
          Set.uIoc (m * x + k) (m * y + k) ⊆ (fun t => m * t + k) '' Set.uIoc x y := by
        intro x y z hz
        rw [Set.mem_uIoc] at hz
        refine ⟨(z - k) / m, ?_, by field_simp; ring⟩
        rw [Set.mem_uIoc]
        rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by rw [lt_div_iff₀ hm]; linarith, by rw [div_le_iff₀ hm]; linarith⟩
        · exact Or.inr ⟨by rw [lt_div_iff₀ hm]; linarith, by rw [div_le_iff₀ hm]; linarith⟩
      have hinj : Function.Injective (fun t => m * t + k) := fun x y h => by
        simp only at h; exact mul_left_cancel₀ hm.ne' (by linarith)
      exact ((Set.disjoint_image_iff hinj).mpr (hEdisj hi hj hij)).mono (hsub _ _) (hsub _ _)
  have hlenF : ∑ i ∈ Finset.range (E.1, F).1, dist (F i).1 (F i).2 < δ := by
    simp only
    calc ∑ i ∈ Finset.range E.1, dist (F i).1 (F i).2
        = m * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => hdistF i)
      _ < m * (δ / m) := mul_lt_mul_of_pos_left (by simpa using hlen) hm
      _ = δ := by field_simp
  simpa [hF] using hδ' (E.1, F) hmemF hlenF

/-- **Absolute continuity transfers along a pointwise equality on the interval.** If `f` is
absolutely continuous on `[a, b]` and `g` agrees with `f` on `uIcc a b`, then `g` is absolutely
continuous on `[a, b]`. -/
theorem AbsolutelyContinuousOnInterval.congr {X : Type*} [PseudoMetricSpace X] {f g : ℝ → X}
    {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : ∀ t ∈ Set.uIcc a b, f t = g t) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have key := hδ' E hE hlen
  simp only [AbsolutelyContinuousOnInterval.disjWithin, Finset.mem_range, mem_ofPred_eq] at hE
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [← hfg _ (hE.1 i (Finset.mem_range.mp hi)).1, ← hfg _ (hE.1 i (Finset.mem_range.mp hi)).2])]
  exact key

/-- **Arc-length line integral over an affine half-interval.** If `η` is absolutely continuous on
`[0, 1]`, the map `t ↦ m t + k` (with `m > 0`) sends `p` to `0` and `q` to `1` with `p < q`, and `γ`
locally coincides with `t ↦ η (m t + k)` throughout `(p, q)`, then the arc-length integrand of `γ`
over `(p, q)` equals that of `η` over `[0, 1]`. The Jacobian `m` of the change of variables cancels
the factor `m` coming from `deriv γ = m • (deriv η ∘ (m · + k))`. -/
private theorem arcLength_half {η γ : ℝ → ℂ} {m k p q : ℝ} (ρ : ℂ → ℝ≥0∞)
    (hη_ac : AbsolutelyContinuousOnInterval η 0 1)
    (hm : 0 < m) (hp : m * p + k = 0) (hq : m * q + k = 1)
    (hagree' : ∀ t ∈ Set.Ioo p q, γ =ᶠ[𝓝 t] fun s => η (m * s + k)) :
    ∫⁻ t in Set.Ioo p q, ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)
      = ∫⁻ u in Set.Icc (0 : ℝ) 1, ρ (η u) * (‖deriv η u‖₊ : ℝ≥0∞) := by
  have hagree : ∀ t ∈ Set.Ioo p q, γ t = η (m * t + k) := fun t ht => (hagree' t ht).eq_of_nhds
  have hηdiff : ∀ᵐ u : ℝ, u ∈ Set.uIcc (0 : ℝ) 1 → DifferentiableAt ℝ η u :=
    hη_ac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm]
  have himg : (fun t => m * t + k) '' Set.Ioo p q = Set.Ioo (0 : ℝ) 1 := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioo]
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      exact ⟨by rw [← hp]; nlinarith, by rw [← hq]; nlinarith⟩
    · intro ⟨hu0, hu1⟩
      refine ⟨(u - k) / m, ⟨?_, ?_⟩, by field_simp; ring⟩
      · rw [lt_div_iff₀ hm]; nlinarith [hp]
      · rw [div_lt_iff₀ hm]; nlinarith [hq]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (f := fun t => m * t + k) (f' := fun _ => m) ?_ ?_ (fun u => ρ (η u) * (‖deriv η u‖₊ : ℝ≥0∞))]
  · -- Transport a.e. differentiability of `η` back through the affine map.
    have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (fun t : ℝ => m * t + k)
        volume volume := by
      have heq : (fun t : ℝ => m * t + k) = (fun x => x + k) ∘ (fun t => m * t) := rfl
      rw [heq]
      refine MeasureTheory.Measure.QuasiMeasurePreserving.comp
        (measurePreserving_add_right volume k).quasiMeasurePreserving ⟨by fun_prop, ?_⟩
      rw [Real.map_volume_mul_left hm.ne']
      exact Measure.smul_absolutelyContinuous
    have hηdiff' : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioo p q)),
        DifferentiableAt ℝ η (m * t + k) := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hqmp.ae hηdiff] with t ht htmem
      refine ht ?_
      rw [Set.uIcc_of_le zero_le_one, Set.mem_Icc]
      obtain ⟨h0, h1⟩ := htmem
      exact ⟨by rw [← hp]; nlinarith, by rw [← hq]; nlinarith⟩
    refine lintegral_congr_ae ?_
    filter_upwards [hηdiff', ae_restrict_mem measurableSet_Ioo] with t htd htmem
    have hderiv : deriv γ t = m • deriv η (m * t + k) := by
      have haff : HasDerivAt (fun s => m * s + k) m t := by
        simpa using ((hasDerivAt_id t).const_mul m).add_const k
      have hc : HasDerivAt (fun s => η (m * s + k)) (m • deriv η (m * t + k)) t := by
        simpa [smul_eq_mul, mul_comm] using! htd.hasDerivAt.scomp t haff
      exact (hc.congr_of_eventuallyEq (hagree' t htmem)).deriv
    rw [hagree t htmem, hderiv,
      show (‖m • deriv η (m * t + k)‖₊ : ℝ≥0∞)
          = ENNReal.ofReal m * (‖deriv η (m * t + k)‖₊ : ℝ≥0∞) from ?_]
    · rw [abs_of_pos hm]; ring
    · set w : ℂ := deriv η (m * t + k) with hw
      rw [show (‖m • w‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖m • w‖ from by
            rw [ofReal_norm, enorm_eq_nnnorm],
          show (‖w‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖w‖ from by
            rw [ofReal_norm, enorm_eq_nnnorm],
          Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm.le,
          ENNReal.ofReal_mul hm.le]
  · intro x _
    exact (by simpa using ((hasDerivAt_id x).const_mul m).add_const k :
      HasDerivAt (fun t : ℝ => m * t + k) m x).hasDerivWithinAt
  · intro s _ t _ hst
    simp only at hst
    exact mul_left_cancel₀ hm.ne' (by linarith : m * s = m * t)

/-- **Concatenation of two absolutely continuous curves with arc-length additivity.** Given
continuous, absolutely continuous curves `γ₁, γ₂ : ℝ → ℂ` on `[0, 1]` with `γ₁ 1 = γ₂ 0`, there is a
continuous, absolutely continuous curve `γ` on `[0, 1]` starting at `γ₁ 0`, ending at `γ₂ 1`, with
image in the union of the two images, and with
`arcLengthLineIntegral ρ γ = arcLengthLineIntegral ρ γ₁ + arcLengthLineIntegral ρ γ₂` for every
density `ρ`. The witness is `γ t = if t ≤ 1/2 then γ₁ (2 t) else γ₂ (2 t - 1)`. -/
theorem exists_concat_curve {γ₁ γ₂ : ℝ → ℂ}
    (h₁c : Continuous γ₁) (h₁ac : AbsolutelyContinuousOnInterval γ₁ 0 1)
    (h₂c : Continuous γ₂) (h₂ac : AbsolutelyContinuousOnInterval γ₂ 0 1)
    (hjoin : γ₁ 1 = γ₂ 0) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧ AbsolutelyContinuousOnInterval γ 0 1 ∧
      γ 0 = γ₁ 0 ∧ γ 1 = γ₂ 1 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ (γ₁ '' Set.Icc 0 1) ∪ (γ₂ '' Set.Icc 0 1)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1,
        γ t ∈ γ₁ '' Set.Ioo 0 1 ∪ {γ₁ 1} ∪ γ₂ '' Set.Ioo 0 1) ∧
      ∀ ρ : ℂ → ℝ≥0∞, arcLengthLineIntegral ρ γ
        = arcLengthLineIntegral ρ γ₁ + arcLengthLineIntegral ρ γ₂ := by
  classical
  set γ : ℝ → ℂ := fun t => if t ≤ 1 / 2 then γ₁ (2 * t) else γ₂ (2 * t - 1) with hγ
  -- Continuity: the two branches meet at `t = 1/2`.
  have hcont : Continuous γ := by
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    intro x hx; subst hx; norm_num; rw [hjoin]
  -- Endpoints.
  have h0 : γ 0 = γ₁ 0 := by simp only [hγ]; rw [if_pos (by norm_num)]; norm_num
  have h1 : γ 1 = γ₂ 1 := by simp only [hγ]; rw [if_neg (by norm_num)]; norm_num
  -- Image in the union of the two images.
  have hrange : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ t ∈ (γ₁ '' Set.Icc 0 1) ∪ (γ₂ '' Set.Icc 0 1) := by
    intro t ht
    by_cases hle : t ≤ 1 / 2
    · rw [hγ]; simp only; rw [if_pos hle]
      exact Or.inl ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, rfl⟩
    · rw [hγ]; simp only; rw [if_neg hle]
      rw [not_le] at hle
      exact Or.inr ⟨2 * t - 1, ⟨by linarith, by linarith [ht.2]⟩, rfl⟩
  -- Interior image: separate the seam point `t = 1/2` from the two open halves.
  have hrange_open : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      γ t ∈ γ₁ '' Set.Ioo 0 1 ∪ {γ₁ 1} ∪ γ₂ '' Set.Ioo 0 1 := by
    intro t ht
    rcases lt_trichotomy t (1 / 2) with hlt | heq | hgt
    · refine Or.inl (Or.inl ?_)
      rw [hγ]; simp only; rw [if_pos hlt.le]
      exact ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, rfl⟩
    · refine Or.inl (Or.inr ?_)
      rw [hγ]; simp only; rw [if_pos heq.le, heq]
      rw [Set.mem_singleton_iff]; norm_num
    · refine Or.inr ?_
      rw [hγ]; simp only; rw [if_neg (by linarith)]
      exact ⟨2 * t - 1, ⟨by linarith, by linarith [ht.2]⟩, rfl⟩
  -- Local coincidence of `γ` with the two affine reparametrizations on the open halves.
  have hev1 : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 2), γ =ᶠ[𝓝 t] fun s => γ₁ (2 * s + 0) := by
    intro t ht
    filter_upwards [Iio_mem_nhds ht.2] with s hs
    rw [Set.mem_Iio] at hs
    simp only [hγ]; rw [if_pos hs.le]; ring_nf
  have hev2 : ∀ t ∈ Set.Ioo (1 / 2 : ℝ) 1, γ =ᶠ[𝓝 t] fun s => γ₂ (2 * s + (-1)) := by
    intro t ht
    filter_upwards [Ioi_mem_nhds ht.1] with s hs
    rw [Set.mem_Ioi] at hs
    simp only [hγ]; rw [if_neg (by linarith)]; ring_nf
  -- Absolute continuity: glue the two affine reparametrizations at `1/2`.
  have hac : AbsolutelyContinuousOnInterval γ 0 1 := by
    refine AbsolutelyContinuousOnInterval.union_of_split (c := 1 / 2)
      (by norm_num) (by norm_num) ?_ ?_
    · -- On `[0, 1/2]`: `γ` agrees with `t ↦ γ₁ (2 t)`.
      refine AbsolutelyContinuousOnInterval.congr
        (f := fun t => γ₁ (2 * t + 0))
        (AbsolutelyContinuousOnInterval.comp_affine (by norm_num) h₁ac ?_) ?_
      · intro t ht
        rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at ht
        rw [Set.uIcc_of_le zero_le_one, Set.mem_Icc]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      · intro t ht
        rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at ht
        simp only [hγ]; rw [if_pos (by linarith [ht.2])]; ring_nf
    · -- On `[1/2, 1]`: `γ` agrees with `t ↦ γ₂ (2 t - 1)`.
      refine AbsolutelyContinuousOnInterval.congr
        (f := fun t => γ₂ (2 * t + (-1)))
        (AbsolutelyContinuousOnInterval.comp_affine (by norm_num) h₂ac ?_) ?_
      · intro t ht
        rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at ht
        rw [Set.uIcc_of_le zero_le_one, Set.mem_Icc]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      · intro t ht
        rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at ht
        simp only [hγ]
        rcases eq_or_lt_of_le ht.1 with hhalf | hhalf
        · -- Seam point `t = 1/2`: use `hjoin`.
          rw [← hhalf]; rw [if_pos (le_refl _)]
          rw [show (2 : ℝ) * (1 / 2) + -1 = 0 by norm_num,
            show (2 : ℝ) * (1 / 2) = 1 by norm_num, hjoin]
        · rw [if_neg (by linarith)]; ring_nf
  refine ⟨γ, hcont, hac, h0, h1, hrange, hrange_open, fun ρ => ?_⟩
  -- Arc-length additivity: split at `1/2`, apply `arcLength_half` on each open half.
  unfold arcLengthLineIntegral
  have hsplit : ∫⁻ t in Set.Icc (0 : ℝ) 1, ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)
      = (∫⁻ t in Set.Ioo (0 : ℝ) (1 / 2), ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞))
        + ∫⁻ t in Set.Ioo (1 / 2 : ℝ) 1, ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
    have hunion : Set.Ioo (0 : ℝ) 1 = Set.Ioo (0 : ℝ) (1 / 2) ∪ Set.Ico (1 / 2 : ℝ) 1 :=
      (Set.Ioo_union_Ico_eq_Ioo (by norm_num) (by norm_num)).symm
    rw [show (∫⁻ t in Set.Icc (0 : ℝ) 1, ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞))
          = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) from by
        rw [← setLIntegral_congr (Ioo_ae_eq_Icc)],
      hunion, lintegral_union measurableSet_Ico]
    · congr 1
      rw [← setLIntegral_congr (Ioo_ae_eq_Ico)]
    · rw [Set.disjoint_left]
      exact fun x hx1 hx2 => absurd hx2.1 (not_le.mpr hx1.2)
  rw [hsplit, arcLength_half ρ h₁ac (by norm_num) (by norm_num) (by norm_num) hev1,
    arcLength_half ρ h₂ac (by norm_num) (by norm_num) (by norm_num) hev2]

end NoWanderingDomains
