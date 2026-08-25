/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Set.Card

/-!
# The Banach indicatrix theorem (continuous one-dimensional, variation ≤ ∫ multiplicity)

For a continuous `f : ℝ → ℝ` restricted to a compact interval `[a, b]`, the **Banach indicatrix**
`N_f(y) := encard {x ∈ [a, b] | f x = y}` (the number, valued in `ℕ∞`, of preimages of `y`) is the
geometric "multiplicity" of the value `y`. Banach's classical theorem (S. Banach, *Sur les lignes
rectifiables et les surfaces dont l'aire est finie*, Fund. Math. **7** (1925)) states the
**indicatrix length formula**

`eVariationOn f (Icc a b) = ∫⁻ y, N_f(y) dy`.

This file builds the inequality direction `eVariationOn f (Icc a b) ≤ ∫⁻ y, N_f(y) dy`, which is the
direction consumed downstream (the swept-area / bounded-variation estimate of the quasiconformal
inverse keystone), together with its specialisations to **injective** maps.

## Why the `≤` direction is the load-bearing one

The keystone application needs, for an **injective** slice, that its real and imaginary parts have
finite total variation bounded by the Lebesgue measure of the slice image. For an injective `f` the
indicatrix is `≤ 1`, so the `≤` direction immediately gives

`eVariationOn f (Icc a b) ≤ ∫⁻ y, N_f(y) dy ≤ ∫⁻ y, 1_{f '' [a,b]}(y) dy = volume (f '' [a, b])`,

so the variation is finite (the continuous image of a compact set has finite measure) and `f` is of
bounded variation on `[a, b]`. No converse direction (which would need a monotone-convergence /
fine-partition construction) is required for this consequence.

## Proof of the `≤` direction

`eVariationOn f s` is, by definition, the supremum over finite monotone partitions
`u₀ ≤ u₁ ≤ ⋯` (all `uᵢ ∈ s`) of the partition sum `∑ᵢ edist (f (u (i+1))) (f (u i))`. The two steps:

1. **Partition-sum as an integral of step multiplicities.** For reals,
   `edist (f (u (i+1))) (f (u i)) = ofReal |f (u (i+1)) - f (u i)| = volume (betw …)`, where
   `betw p q := Ioo (min p q) (max p q)` is the open interval of values strictly between `p` and
   `q`. Hence (by linearity of the Lebesgue integral over a finite sum)
   `∑ᵢ edist … = ∫⁻ y, ∑ᵢ 1_{betw (f (u i)) (f (u (i+1)))}(y) dy`.

2. **The step multiplicity is dominated by the indicatrix.** Fix `y`. For each index `i` with
   `y ∈ betw (f (u i)) (f (u (i+1)))`, the **intermediate value theorem** (continuity of `f`)
   produces a witness `x_i ∈ Ioo (u i) (u (i+1))` with `f x_i = y`; the open intervals
   `Ioo (u i) (u (i+1))` are pairwise disjoint (monotonicity of `u`), so the witnesses are distinct
   and all lie in `[a, b]`. This injects the active index set into the fibre
   `{x ∈ [a, b] | f x = y}`, giving `∑ᵢ 1_{betw …}(y) ≤ N_f(y)` pointwise.

Monotonicity of the Lebesgue integral (no measurability of `N_f` is needed for this direction) then
yields `∑ᵢ edist … ≤ ∫⁻ N_f`, and taking the supremum over partitions gives the result.

## Main results

* `NoWanderingDomains.eVariationOn_le_lintegral_indicatrix` — the inequality direction of the Banach
  indicatrix theorem: `eVariationOn f (Icc a b) ≤ ∫⁻ y, N_f(y) dy`.
* `NoWanderingDomains.eVariationOn_le_volume_image_of_injOn` — for `f` continuous and injective on
  `[a, b]`, `eVariationOn f (Icc a b) ≤ volume (f '' Icc a b)`; the indicatrix collapses to
  `≤ 1`.
* `NoWanderingDomains.boundedVariationOn_Icc_of_injOn_continuousOn` — such an `f` is of bounded
  variation on `[a, b]`; the continuous image of a compact interval has finite measure.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace NoWanderingDomains

/-! ## The open interval of values strictly between two reals -/

/-- `betw p q` is the open interval of reals strictly between `p` and `q` (in either order). Its
Lebesgue measure is `|q - p|`, matching `edist q p` for reals; it is the value-set swept as `f`
moves between `p` and `q`. -/
noncomputable def betw (p q : ℝ) : Set ℝ := Ioo (min p q) (max p q)

lemma measurableSet_betw (p q : ℝ) : MeasurableSet (betw p q) := measurableSet_Ioo

/-- The Lebesgue measure of `betw p q` is `|q - p|`. -/
lemma volume_betw (p q : ℝ) : volume (betw p q) = ENNReal.ofReal |q - p| := by
  unfold betw
  rw [Real.volume_Ioo]
  rcases le_total p q with h | h
  · rw [min_eq_left h, max_eq_right h, abs_of_nonneg (by linarith)]
  · rw [min_eq_right h, max_eq_left h, abs_of_nonpos (by linarith), neg_sub]

/-- For reals, `edist q p = ofReal |q - p|`. -/
lemma edist_real (p q : ℝ) : edist q p = ENNReal.ofReal |q - p| := by
  rw [edist_dist, Real.dist_eq]

/-- **Intermediate value witness.** If `y` is strictly between `f c` and `f d` (i.e. `y ∈ betw (f c)
(f d)`) and `f` is continuous on `[c, d]` with `c ≤ d`, then `f` attains `y` at some interior point
`x ∈ Ioo c d`. -/
lemma exists_mem_Ioo_of_betw {f : ℝ → ℝ} {c d : ℝ} (hcd : c ≤ d)
    (hcont : ContinuousOn f (Icc c d)) {y : ℝ} (hy : y ∈ betw (f c) (f d)) :
    ∃ x ∈ Ioo c d, f x = y := by
  unfold betw at hy
  rcases le_total (f c) (f d) with h | h
  · rw [min_eq_left h, max_eq_right h] at hy
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo hcd hcont hy
    exact ⟨x, hx, hfx⟩
  · rw [min_eq_right h, max_eq_left h] at hy
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' hcd hcont hy
    exact ⟨x, hx, hfx⟩

/-! ## The Banach indicatrix and the inequality direction -/

/-- **The Banach indicatrix** `N_f(y)` on `[a, b]`: the (extended-natural) number of preimages of
`y` under `f` lying in `[a, b]`, coerced into `ℝ≥0∞` for Lebesgue integration. -/
noncomputable def indicatrix (f : ℝ → ℝ) (a b : ℝ) (y : ℝ) : ℝ≥0∞ :=
  (Set.encard {x ∈ Set.Icc a b | f x = y} : ℝ≥0∞)

/-- **The partition-sum is the integral of the step-multiplicity function.** For any finite monotone
partition the variation partition sum `∑ᵢ edist (f (u (i+1))) (f (u i))` equals the Lebesgue
integral over `y` of the number of partition intervals whose `f`-image strictly straddles `y`. -/
lemma partition_sum_eq_lintegral_mult (f : ℝ → ℝ) (u : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
      = ∫⁻ y, ∑ i ∈ Finset.range n,
          (betw (f (u i)) (f (u (i + 1)))).indicator (fun _ => (1 : ℝ≥0∞)) y := by
  rw [lintegral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [lintegral_indicator_const (measurableSet_betw _ _), one_mul, volume_betw, edist_real]
  · exact fun i _ => measurable_const.indicator (measurableSet_betw _ _)

/-- **The step-multiplicity is dominated by the indicatrix.** For a monotone partition of `[a, b]`
of a function continuous on `[a, b]`, the number of partition intervals whose image straddles `y` is
at most the number of preimages of `y` in `[a, b]`. The witnesses supplied by the intermediate value
theorem inject the active index set into the fibre. -/
lemma mult_le_indicatrix {f : ℝ → ℝ} {a b : ℝ} (hcont : ContinuousOn f (Icc a b))
    {u : ℕ → ℝ} (hu : Monotone u) (hus : ∀ i, u i ∈ Icc a b) (n : ℕ) (y : ℝ) :
    (∑ i ∈ Finset.range n,
        (betw (f (u i)) (f (u (i + 1)))).indicator (fun _ => (1 : ℝ≥0∞)) y)
      ≤ indicatrix f a b y := by
  classical
  unfold indicatrix
  -- `S` = active indices: partition intervals whose image straddles `y`.
  set S := (Finset.range n).filter (fun i => y ∈ betw (f (u i)) (f (u (i + 1)))) with hS
  have hLHS : (∑ i ∈ Finset.range n,
      (betw (f (u i)) (f (u (i + 1)))).indicator (fun _ => (1 : ℝ≥0∞)) y) = (S.card : ℝ≥0∞) := by
    rw [hS, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : y ∈ betw (f (u i)) (f (u (i + 1)))
    · rw [Set.indicator_of_mem h, if_pos h]
    · rw [Set.indicator_of_notMem h, if_neg h]
  rw [hLHS]
  -- IVT witness for each active index.
  have hwit : ∀ i ∈ S, ∃ x ∈ Ioo (u i) (u (i + 1)), f x = y := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    have hcd : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have hcont' : ContinuousOn f (Icc (u i) (u (i + 1))) :=
      hcont.mono (Set.Icc_subset_Icc (hus i).1 (hus (i + 1)).2)
    exact exists_mem_Ioo_of_betw hcd hcont' hi.2
  choose φ hφ_mem hφ_eq using hwit
  have hcard : (S.card : ℝ≥0∞) = ((↑S : Set ℕ).encard : ℝ≥0∞) := by
    rw [Set.encard_coe_eq_coe_finsetCard]; rfl
  rw [hcard]
  -- Total witness function (default `a` off `S`).
  set Φ : ℕ → ℝ := fun i => if hi : i ∈ S then φ i hi else a with hΦ
  have hImgSub : Φ '' (↑S : Set ℕ) ⊆ {x ∈ Set.Icc a b | f x = y} := by
    rintro z ⟨i, hi, rfl⟩
    have hiS : i ∈ S := hi
    simp only [hΦ, dif_pos hiS]
    have hxIoo := hφ_mem i hiS
    exact ⟨⟨le_of_lt (lt_of_le_of_lt (hus i).1 hxIoo.1),
        le_of_lt (lt_of_lt_of_le hxIoo.2 (hus (i + 1)).2)⟩, hφ_eq i hiS⟩
  have hInj : Set.InjOn Φ (↑S : Set ℕ) := by
    intro i hi j hj hij
    rcases lt_trichotomy i j with h | h | h
    · exfalso
      have hiS : i ∈ S := hi
      have hjS : j ∈ S := hj
      simp only [hΦ, dif_pos hiS, dif_pos hjS] at hij
      have hxi := hφ_mem i hiS
      have hxj := hφ_mem j hjS
      have h1 : u (i + 1) ≤ u j := hu (by omega)
      have hlt : φ i hiS < φ j hjS := lt_of_lt_of_le hxi.2 (le_trans h1 (le_of_lt hxj.1))
      rw [hij] at hlt; exact lt_irrefl _ hlt
    · exact h
    · exfalso
      have hiS : i ∈ S := hi
      have hjS : j ∈ S := hj
      simp only [hΦ, dif_pos hiS, dif_pos hjS] at hij
      have hxi := hφ_mem i hiS
      have hxj := hφ_mem j hjS
      have h1 : u (j + 1) ≤ u i := hu (by omega)
      have hlt : φ j hjS < φ i hiS := lt_of_lt_of_le hxj.2 (le_trans h1 (le_of_lt hxi.1))
      rw [hij] at hlt; exact lt_irrefl _ hlt
  calc ((↑S : Set ℕ).encard : ℝ≥0∞)
      = ((Φ '' (↑S : Set ℕ)).encard : ℝ≥0∞) := by rw [hInj.encard_image]
    _ ≤ ((Set.encard {x ∈ Set.Icc a b | f x = y}) : ℝ≥0∞) := by
        exact_mod_cast Set.encard_le_encard hImgSub

/-- **The Banach indicatrix theorem (inequality direction).** For a function continuous on
`[a, b]`, the total variation is bounded by the integral of the Banach indicatrix:

`eVariationOn f (Icc a b) ≤ ∫⁻ y, N_f(y) dy`, where `N_f(y) = encard {x ∈ [a, b] | f x = y}`.

This is the load-bearing direction of Banach's 1925 theorem; the reverse inequality (an equality
for continuous `f`) requires a fine-partition monotone-convergence construction and is not needed
for the swept-area estimate downstream. -/
theorem eVariationOn_le_lintegral_indicatrix {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b)) :
    eVariationOn f (Icc a b) ≤ ∫⁻ y, indicatrix f a b y := by
  refine iSup_le ?_
  rintro ⟨n, u, humono, hus⟩
  simp only
  rw [partition_sum_eq_lintegral_mult]
  exact lintegral_mono (fun y => mult_le_indicatrix hcont humono hus n y)

/-! ## Injective specialisation: variation bounded by image measure -/

/-- **Injective collapse of the indicatrix.** If `f` is injective on `[a, b]`, every fibre has at
most one point, so `N_f(y) ≤ 1_{f '' [a,b]}(y)` pointwise (and `N_f(y) = 0` off the image). -/
lemma indicatrix_le_indicator_image_of_injOn {f : ℝ → ℝ} {a b : ℝ}
    (hinj : Set.InjOn f (Icc a b)) (y : ℝ) :
    indicatrix f a b y ≤ (f '' Set.Icc a b).indicator (fun _ => (1 : ℝ≥0∞)) y := by
  unfold indicatrix
  by_cases hy : y ∈ f '' Set.Icc a b
  · rw [Set.indicator_of_mem hy]
    have hsub : Set.encard {x ∈ Set.Icc a b | f x = y} ≤ 1 := by
      rw [Set.encard_le_one_iff]
      intro p q hp hq
      simp only [Set.mem_ofPred_eq] at hp hq
      exact hinj hp.1 hq.1 (hp.2.trans hq.2.symm)
    calc (Set.encard {x ∈ Set.Icc a b | f x = y} : ℝ≥0∞) ≤ ((1 : ℕ∞) : ℝ≥0∞) := by
          exact_mod_cast hsub
      _ = 1 := by simp
  · rw [Set.indicator_of_notMem hy]
    have hempty : {x ∈ Set.Icc a b | f x = y} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hx hfx => hy ⟨x, hx, hfx⟩
    rw [hempty]; simp

/-- **Variation bounded by image measure (injective continuous case).** For `f` continuous
and injective on `[a, b]`, `eVariationOn f (Icc a b) ≤ volume (f '' Icc a b)`. The Banach indicatrix
collapses to `≤ 1` and integrates to the image measure. -/
theorem eVariationOn_le_volume_image_of_injOn {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b)) (hinj : Set.InjOn f (Icc a b)) :
    eVariationOn f (Icc a b) ≤ volume (f '' Set.Icc a b) := by
  have hms : MeasurableSet (f '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hcont).measurableSet
  calc eVariationOn f (Icc a b)
      ≤ ∫⁻ y, indicatrix f a b y := eVariationOn_le_lintegral_indicatrix hcont
    _ ≤ ∫⁻ y, (f '' Set.Icc a b).indicator (fun _ => (1 : ℝ≥0∞)) y :=
        lintegral_mono (fun y => indicatrix_le_indicator_image_of_injOn hinj y)
    _ = volume (f '' Set.Icc a b) := by rw [lintegral_indicator_const hms, one_mul]

/-- **Bounded variation of an injective continuous map on a compact interval.** The
continuous image of `[a, b]` is compact, hence of finite Lebesgue measure, so the variation is
finite. -/
theorem boundedVariationOn_Icc_of_injOn_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b)) (hinj : Set.InjOn f (Icc a b)) :
    BoundedVariationOn f (Set.Icc a b) := by
  have hcompact : IsCompact (f '' Set.Icc a b) := isCompact_Icc.image_of_continuousOn hcont
  have hfin : volume (f '' Set.Icc a b) < ⊤ := hcompact.measure_lt_top
  have hle := eVariationOn_le_volume_image_of_injOn hcont hinj
  exact ne_top_of_le_ne_top hfin.ne hle

end NoWanderingDomains
