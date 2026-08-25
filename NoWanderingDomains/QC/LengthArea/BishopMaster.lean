/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.LengthArea.BishopRengel

/-!
# The master per-height Rengel estimates

The two master estimates of the classical (Bishop / Ahlfors / Lehto–Virtanen / Väisälä)
forward length–area analysis of a geometric `K`-quasiconformal homeomorphism, both derived
from the strip increment bounds and the monotone image-area profiles of the Rengel bricks:

* `qc_master_sum_sq_div_le_horizontal` / `_vertical` — the **contact-allowed per-height
  Rengel sum**: for an *ordered* family of intervals inside a window (adjacent intervals may
  touch), the sum of squared slice chords over interval lengths is at most `2K` times the
  profile derivative. The contact-allowed shape is what lets a raw partition of an interval
  be fed in directly; it is the single two-dimensional input to the slice variation and
  slice energy bounds.
* `AxisRectModulusBound.horizontal_family_sq_sum_le` / `vertical_family_sq_sum_le` — the
  **one-sided family estimate at a good height**: for *pairwise disjoint closed* intervals
  and a height whose segment has null image, the same sum is at most `K` times the profile
  derivative. This sharper, one-sided form feeds the ε–δ criterion of slice absolute
  continuity.

The two estimates differ genuinely in shape (interval families and constants), but share
all their two-dimensional content through the strip increment bounds
`AxisRectModulusBound.horizontal_strip_sep_sq_le`/`vertical_strip_sep_sq_le` and the profile
lemmas.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace NoWanderingDomains

/-- **Master per-height Rengel sum (horizontal slices; ordered, contact-allowed
families).** Let `f` be geometric `K`-quasiconformal and let `y` be a height above `σ` at
which the horizontal image-area profile of the window `[α,β]` is differentiable. For every
finite ordered family of intervals `[A i, B i] ⊆ [α,β]` — ordered means `B i ≤ A j` for
`i < j`, so adjacent intervals may *touch* — the per-height Rengel sum obeys
`∑ i, ‖f ⟨B i, y⟩ − f ⟨A i, y⟩‖²/(B i − A i) ≤ 2K · Φ′(y)`.

The chord `‖f ⟨B i, y⟩ − f ⟨A i, y⟩‖` replaces the classical image-edge length: it is
weaker per interval but sufficient, because the total variation of a slice is by definition
a supremum of chord sums.

*Proof sketch.* Write `wᵢ := B i − A i > 0`, `rᵢ` for the chords, `D := deriv Φ y ≥ 0`. It
suffices to prove `∑ (max (rᵢ − ε) 0)²/wᵢ ≤ K(2D + ε′)` for all `ε, ε′ > 0`, since
`(max (r − ε) 0)² ≥ r² − 2rε` and both corrections vanish as `ε, ε′ → 0`
(`le_of_forall_pos_le_add`). Fix `ε, ε′`:
1. `f` is uniformly continuous on a compact window containing all the rectangles below;
   choose `θ > 0` with oscillation `≤ ε/2` at scale `θ`.
2. Differentiability at `y` gives `δ₀ > 0` with `Φ(y+δ) − Φ(y−δ) ≤ (2D + ε′)δ` for
   `0 < δ < δ₀` (two-sided difference quotient of `HasDerivAt`).
3. Put `δ = η := (1/2)·min {δ₀, θ/2, min wᵢ/3, y − σ} > 0`.
4. The shrunken rectangles `R′ᵢ := [A i + η, B i − η] × [y, y+δ]` are pairwise disjoint
   closed rectangles even where the original intervals touch (`B i − η < B i ≤ A j < A j + η`).
5. Every point of the image of a vertical edge of `R′ᵢ` is within `ε/2` of the corner image
   (`dist ⟨A i + η, τ⟩ ⟨A i, y⟩ ≤ η + δ ≤ θ`), so for `rᵢ > ε` the two edge images are
   separated by `rᵢ − ε` (triangle inequality); indices with `rᵢ ≤ ε` contribute `0`.
6. The strip increment bound (`AxisRectModulusBound.horizontal_strip_sep_sq_le`) gives
   `(rᵢ − ε)² · δ/(K·wᵢ) ≤ (rᵢ − ε)² · δ/(K·(wᵢ − 2η)) ≤ area (f '' R′ᵢ)`.
7. The compact images `f '' R′ᵢ` are pairwise disjoint (injectivity) inside
   `f '' ([α,β] × [y, y+δ])`, so their areas sum below the two-sided profile bound
   (`imageArea_strip_le_profileY_diff`): `∑ᵢ ≤ Φ(y+δ) − Φ(y−δ) ≤ (2D + ε′)δ`.
8. Divide by `δ/K`.
-/
theorem qc_master_sum_sq_div_le_horizontal {f : ℂ → ℂ} {K : ℝ} (hf : AxisRectModulusBound f K)
    {α β σ y : ℝ} (hσy : σ < y)
    (hΦ : DifferentiableAt ℝ (imageAreaProfileY f α β σ) y)
    {m : ℕ} {A B : Fin m → ℝ}
    (hAB : ∀ i, A i < B i) (hord : ∀ i j : Fin m, i < j → B i ≤ A j)
    (hmem : ∀ i, α ≤ A i ∧ B i ≤ β) :
    ∑ i, ‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ ^ 2 / (B i - A i)
      ≤ 2 * K * deriv (imageAreaProfileY f α β σ) y := by
  have hcont : Continuous f := hf.2.1.continuous
  have hinj : Function.Injective f := hf.2.1.injective
  have hK1 : 1 ≤ K := hf.1
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hD0 : 0 ≤ deriv (imageAreaProfileY f α β σ) y :=
    (monotone_imageAreaProfileY hcont α β σ).deriv_nonneg
  -- the empty family is trivial
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact mul_nonneg (mul_nonneg (by norm_num) hK0.le) hD0
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  -- distance between explicit complex points
  have hdist_mk : ∀ a b u v : ℝ, dist (⟨a, b⟩ : ℂ) ⟨u, v⟩ ≤ |a - u| + |b - v| := by
    intro a b u v
    calc dist (⟨a, b⟩ : ℂ) ⟨u, v⟩
        ≤ dist (⟨a, b⟩ : ℂ) ⟨u, b⟩ + dist (⟨u, b⟩ : ℂ) ⟨u, v⟩ := dist_triangle _ _ _
      _ = |a - u| + |b - v| := by
          have e1 : dist (⟨a, b⟩ : ℂ) ⟨u, b⟩ = |a - u| :=
            (Complex.dist_of_im_eq
              (show (⟨a, b⟩ : ℂ).im = (⟨u, b⟩ : ℂ).im from rfl)).trans (Real.dist_eq a u)
          have e2 : dist (⟨u, b⟩ : ℂ) ⟨u, v⟩ = |b - v| :=
            (Complex.dist_of_re_eq
              (show (⟨u, b⟩ : ℂ).re = (⟨u, v⟩ : ℂ).re from rfl)).trans (Real.dist_eq b v)
          rw [e1, e2]
  -- a shortest interval
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin m => B i - A i) Finset.univ_nonempty
  -- ★: the shrunken-chord estimate, for every positive `ε` (chord shrink) and `ε'`
  -- (derivative slack)
  have star : ∀ ε : ℝ, 0 < ε → ∀ ε' : ℝ, 0 < ε' →
      ∑ i, (max (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ε) 0) ^ 2 / (B i - A i)
        ≤ K * (2 * deriv (imageAreaProfileY f α β σ) y + ε') := by
    intro ε hε ε' hε'
    -- 1. modulus of continuity on the compact window
    have hUC : UniformContinuousOn f (axisRect α β y (y + 1)) :=
      (isCompact_axisRect α β y (y + 1)).uniformContinuousOn_of_continuous
        hcont.continuousOn
    obtain ⟨θ, hθpos, hθ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) (half_pos hε)
    -- 2. two-sided derivative window
    obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        imageAreaProfileY f α β σ (y + δ) - imageAreaProfileY f α β σ (y - δ)
          ≤ (2 * deriv (imageAreaProfileY f α β σ) y + ε') * δ := by
      have hslope : Filter.Tendsto (slope (imageAreaProfileY f α β σ) y)
          (nhdsWithin y {y}ᶜ) (nhds (deriv (imageAreaProfileY f α β σ) y)) :=
        hasDerivAt_iff_tendsto_slope.mp hΦ.hasDerivAt
      have hev : ∀ᶠ v in nhdsWithin y {y}ᶜ,
          dist (slope (imageAreaProfileY f α β σ) y v)
            (deriv (imageAreaProfileY f α β σ) y) < ε' / 2 :=
        Metric.tendsto_nhds.mp hslope (ε' / 2) (half_pos hε')
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
      obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hev
      refine ⟨δ₀, hδ₀pos, fun δ hδp hδlt => ?_⟩
      have hplus : dist (slope (imageAreaProfileY f α β σ) y (y + δ))
          (deriv (imageAreaProfileY f α β σ) y) < ε' / 2 := by
        refine hδ₀ ?_ ?_
        · rw [Real.dist_eq, show y + δ - y = δ by ring, abs_of_pos hδp]; exact hδlt
        · exact Set.mem_compl_singleton_iff.mpr (ne_of_gt (by linarith))
      have hminus : dist (slope (imageAreaProfileY f α β σ) y (y - δ))
          (deriv (imageAreaProfileY f α β σ) y) < ε' / 2 := by
        refine hδ₀ ?_ ?_
        · rw [Real.dist_eq, show y - δ - y = -δ by ring, abs_neg, abs_of_pos hδp]
          exact hδlt
        · exact Set.mem_compl_singleton_iff.mpr (ne_of_lt (by linarith))
      have hsplus : (imageAreaProfileY f α β σ (y + δ) - imageAreaProfileY f α β σ y) / δ
          < deriv (imageAreaProfileY f α β σ) y + ε' / 2 := by
        rw [Real.dist_eq, abs_sub_lt_iff] at hplus
        have h2 := hplus.1
        rwa [slope_def_field, show y + δ - y = δ by ring, sub_lt_iff_lt_add'] at h2
      have hsminus : (imageAreaProfileY f α β σ y - imageAreaProfileY f α β σ (y - δ)) / δ
          < deriv (imageAreaProfileY f α β σ) y + ε' / 2 := by
        rw [Real.dist_eq, abs_sub_lt_iff] at hminus
        have h2 := hminus.1
        rwa [slope_def_field, show y - δ - y = -δ by ring, div_neg, ← neg_div, neg_sub,
          sub_lt_iff_lt_add'] at h2
      have eplus := (div_lt_iff₀ hδp).mp hsplus
      have eminus := (div_lt_iff₀ hδp).mp hsminus
      nlinarith [eplus, eminus]
    -- 3. choice of the scale
    set M : ℝ := min (min δ₀ θ) (min (B i₀ - A i₀) (min (y - σ) 1)) with hM
    have hMδ₀ : M ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
    have hMθ : M ≤ θ := (min_le_left _ _).trans (min_le_right _ _)
    have hMw : M ≤ B i₀ - A i₀ := (min_le_right _ _).trans (min_le_left _ _)
    have hMyσ : M ≤ y - σ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hM1 : M ≤ 1 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hMpos : 0 < M := by
      refine lt_min (lt_min hδ₀pos hθpos)
        (lt_min (sub_pos.mpr (hAB i₀)) (lt_min (by linarith) one_pos))
    set δ : ℝ := M / 4 with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; linarith
    have hδδ₀ : δ < δ₀ := by rw [hδdef]; linarith
    have h2δθ : 2 * δ < θ := by rw [hδdef]; linarith
    have h2δw : ∀ i : Fin m, 2 * δ < B i - A i := fun i => by
      rw [hδdef]
      have := hi₀ i (Finset.mem_univ i)
      linarith
    have hσδ : σ ≤ y - δ := by rw [hδdef]; linarith
    have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
    -- 4. oscillation control at scale `δ` inside the window
    have hosc : ∀ x₁ x₂ τ₁ τ₂ : ℝ, α ≤ x₁ → x₁ ≤ β → α ≤ x₂ → x₂ ≤ β →
        y ≤ τ₁ → τ₁ ≤ y + 1 → y ≤ τ₂ → τ₂ ≤ y + 1 →
        |x₁ - x₂| ≤ δ → |τ₁ - τ₂| ≤ δ →
        dist (f ⟨x₁, τ₁⟩) (f ⟨x₂, τ₂⟩) ≤ ε / 2 := by
      intro x₁ x₂ τ₁ τ₂ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      have hd : dist (⟨x₁, τ₁⟩ : ℂ) ⟨x₂, τ₂⟩ < θ :=
        lt_of_le_of_lt (hdist_mk x₁ τ₁ x₂ τ₂) (by linarith)
      exact le_of_lt (hθ _ ⟨⟨h1, h2⟩, h5, h6⟩ _ ⟨⟨h3, h4⟩, h7, h8⟩ hd)
    -- 5. volumes of the shrunken-rectangle images
    have hbig_ne : volume (f '' axisRect α β y (y + δ)) ≠ ⊤ :=
      (((isCompact_axisRect α β y (y + δ)).image hcont).measure_lt_top).ne
    have hfin : ∀ i : Fin m,
        volume (f '' axisRect (A i + δ) (B i - δ) y (y + δ)) ≠ ⊤ := fun i =>
      (((isCompact_axisRect (A i + δ) (B i - δ) y (y + δ)).image hcont).measure_lt_top).ne
    have hRsub : ∀ i : Fin m,
        axisRect (A i + δ) (B i - δ) y (y + δ) ⊆ axisRect α β y (y + 1) := by
      intro i z hz
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
      exact ⟨⟨by linarith [(hmem i).1], by linarith [(hmem i).2]⟩, h3, by linarith⟩
    have hRsubδ : ∀ i : Fin m,
        axisRect (A i + δ) (B i - δ) y (y + δ) ⊆ axisRect α β y (y + δ) := by
      intro i z hz
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
      exact ⟨⟨by linarith [(hmem i).1], by linarith [(hmem i).2]⟩, h3, h4⟩
    -- 6. pairwise disjointness of the shrunken rectangles and their images
    have hRdisj : ∀ i j : Fin m, i ≠ j →
        Disjoint (axisRect (A i + δ) (B i - δ) y (y + δ))
          (axisRect (A j + δ) (B j - δ) y (y + δ)) := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · rw [Set.disjoint_left]
        intro z hzi hzj
        have h1 : z.re ≤ B i - δ := hzi.1.2
        have h2 : A j + δ ≤ z.re := hzj.1.1
        have h3 : B i ≤ A j := hord i j hlt
        linarith
      · rw [Set.disjoint_left]
        intro z hzi hzj
        have h1 : z.re ≤ B j - δ := hzj.1.2
        have h2 : A i + δ ≤ z.re := hzi.1.1
        have h3 : B j ≤ A i := hord j i hlt
        linarith
    -- 7. the disjoint sum of image areas is below the profile increment
    have hsum_vol : ∑ i : Fin m,
        (volume (f '' axisRect (A i + δ) (B i - δ) y (y + δ))).toReal
          ≤ (volume (f '' axisRect α β y (y + δ))).toReal := by
      rw [← ENNReal.toReal_sum (fun i _ => hfin i)]
      refine ENNReal.toReal_mono hbig_ne ?_
      have hdisj' : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m)))
          (fun i => f '' axisRect (A i + δ) (B i - δ) y (y + δ)) := fun i _ j _ hij =>
        Set.disjoint_image_of_injective hinj (hRdisj i j hij)
      rw [← measure_biUnion_finset hdisj' fun i _ =>
        (((isCompact_axisRect (A i + δ) (B i - δ) y (y + δ)).image
          hcont).isClosed.measurableSet)]
      exact measure_mono (Set.iUnion₂_subset fun i _ => Set.image_mono (hRsubδ i))
    -- 8. per-rectangle chord–area estimate
    have hterm : ∀ i : Fin m,
        (max (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ε) 0) ^ 2 / (B i - A i)
          ≤ (K / δ) * (volume (f '' axisRect (A i + δ) (B i - δ) y (y + δ))).toReal := by
      intro i
      have hwi : 0 < B i - A i := sub_pos.mpr (hAB i)
      have hKδ : 0 ≤ K / δ := (div_pos hK0 hδpos).le
      rcases le_or_gt (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖) ε with hle | hlt
      · rw [max_eq_right (by linarith), zero_pow two_ne_zero, zero_div]
        exact mul_nonneg hKδ ENNReal.toReal_nonneg
      · rw [max_eq_left (by linarith)]
        have hcd' : A i + δ < B i - δ := by linarith [h2δw i]
        have hAi := (hmem i).1
        have hBi := (hmem i).2
        have hABi := hAB i
        have h2w := h2δw i
        -- separation of the shrunken vertical-edge images
        have hsep : ∀ τ₁ ∈ Set.Icc y (y + δ), ∀ τ₂ ∈ Set.Icc y (y + δ),
            ‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ε ≤ dist (f ⟨A i + δ, τ₁⟩) (f ⟨B i - δ, τ₂⟩) := by
          intro τ₁ hτ₁ τ₂ hτ₂
          obtain ⟨hτ₁l, hτ₁r⟩ := hτ₁
          obtain ⟨hτ₂l, hτ₂r⟩ := hτ₂
          have h1 : dist (f ⟨A i + δ, τ₁⟩) (f ⟨A i, y⟩) ≤ ε / 2 := by
            refine hosc (A i + δ) (A i) τ₁ y (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith) le_rfl (by linarith) ?_ ?_
            · rw [abs_le]; constructor <;> [linarith; linarith]
            · rw [abs_le]; constructor <;> [linarith; linarith]
          have h2 : dist (f ⟨B i - δ, τ₂⟩) (f ⟨B i, y⟩) ≤ ε / 2 := by
            refine hosc (B i - δ) (B i) τ₂ y (by linarith) (by linarith) (by linarith)
              (by linarith) (by linarith) (by linarith) le_rfl (by linarith) ?_ ?_
            · rw [abs_le]; constructor <;> [linarith; linarith]
            · rw [abs_le]; constructor <;> [linarith; linarith]
          have htri : dist (f ⟨B i, y⟩) (f ⟨A i, y⟩)
              ≤ dist (f ⟨B i, y⟩) (f ⟨B i - δ, τ₂⟩)
                + dist (f ⟨B i - δ, τ₂⟩) (f ⟨A i + δ, τ₁⟩)
                + dist (f ⟨A i + δ, τ₁⟩) (f ⟨A i, y⟩) := dist_triangle4 _ _ _ _
          have hnorm : ‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ = dist (f ⟨B i, y⟩) (f ⟨A i, y⟩) :=
            (dist_eq_norm _ _).symm
          have ec1 : dist (f ⟨B i, y⟩) (f ⟨B i - δ, τ₂⟩)
              = dist (f ⟨B i - δ, τ₂⟩) (f ⟨B i, y⟩) := dist_comm _ _
          have ec2 : dist (f ⟨B i - δ, τ₂⟩) (f ⟨A i + δ, τ₁⟩)
              = dist (f ⟨A i + δ, τ₁⟩) (f ⟨B i - δ, τ₂⟩) := dist_comm _ _
          linarith
        have hstrip := hf.horizontal_strip_sep_sq_le hcd' hδpos (by linarith) hsep
        -- widen the denominator from the shrunken width to the full width
        have hmono : (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ε) ^ 2 * (δ / (K * (B i - A i)))
            ≤ (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ε) ^ 2
              * (δ / (K * ((B i - δ) - (A i + δ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact div_le_div_of_nonneg_left hδpos.le
            (mul_pos hK0 (by linarith)) (mul_le_mul_of_nonneg_left (by linarith) hK0.le)
        have hchain := hmono.trans hstrip
        have hKne : K ≠ 0 := hK0.ne'
        have hδne : δ ≠ 0 := hδpos.ne'
        have hwne : B i - A i ≠ 0 := hwi.ne'
        calc (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ε) ^ 2 / (B i - A i)
            = (K / δ) * ((‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ε) ^ 2
                * (δ / (K * (B i - A i)))) := by
              field_simp
          _ ≤ (K / δ)
                * (volume (f '' axisRect (A i + δ) (B i - δ) y (y + δ))).toReal :=
              mul_le_mul_of_nonneg_left hchain hKδ
    -- 9. sum, compare with the profile increment, divide by `δ/K`
    have hδne : δ ≠ 0 := hδpos.ne'
    calc ∑ i, (max (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ε) 0) ^ 2 / (B i - A i)
        ≤ ∑ i, (K / δ)
            * (volume (f '' axisRect (A i + δ) (B i - δ) y (y + δ))).toReal :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (K / δ) * ∑ i,
            (volume (f '' axisRect (A i + δ) (B i - δ) y (y + δ))).toReal := by
          rw [Finset.mul_sum]
      _ ≤ (K / δ) * ((2 * deriv (imageAreaProfileY f α β σ) y + ε') * δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_pos hK0 hδpos).le
          calc ∑ i, (volume (f '' axisRect (A i + δ) (B i - δ) y (y + δ))).toReal
              ≤ (volume (f '' axisRect α β y (y + δ))).toReal := hsum_vol
            _ ≤ imageAreaProfileY f α β σ (y + δ) - imageAreaProfileY f α β σ (y - δ) :=
                imageArea_strip_le_profileY_diff hcont hinj hδpos hσδ
            _ ≤ (2 * deriv (imageAreaProfileY f α β σ) y + ε') * δ := hδ₀ δ hδpos hδδ₀
      _ = K * (2 * deriv (imageAreaProfileY f α β σ) y + ε') := by
          field_simp
  -- the `ε, ε' → 0` reduction
  refine le_of_forall_pos_le_add fun ρ hρ => ?_
  have hknn : (0 : ℝ) ≤ ∑ i, ‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ / (B i - A i) :=
    Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (sub_pos.mpr (hAB i)).le
  set k : ℝ := ∑ i, ‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ / (B i - A i) with hkdef
  have hεp : 0 < ρ / (4 * (k + 1)) := div_pos hρ (by linarith)
  have hε'p : 0 < ρ / (2 * K) := div_pos hρ (by linarith)
  have hstar := star _ hεp _ hε'p
  have hsplit : ∀ i : Fin m,
      ‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ ^ 2 / (B i - A i)
        ≤ (max (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ρ / (4 * (k + 1))) 0) ^ 2 / (B i - A i)
          + 2 * (ρ / (4 * (k + 1))) * (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ / (B i - A i)) := by
    intro i
    have hwi : 0 < B i - A i := sub_pos.mpr (hAB i)
    have hr : (0 : ℝ) ≤ ‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ := norm_nonneg _
    have key : ‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ ^ 2
        ≤ (max (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ρ / (4 * (k + 1))) 0) ^ 2
          + 2 * (ρ / (4 * (k + 1))) * ‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ := by
      rcases le_or_gt (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖) (ρ / (4 * (k + 1))) with h | h
      · rw [max_eq_right (by linarith)]
        nlinarith [mul_nonneg hr (sub_nonneg.mpr h), mul_nonneg hεp.le hr]
      · rw [max_eq_left (by linarith)]
        nlinarith [sq_nonneg (ρ / (4 * (k + 1)))]
    calc ‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ ^ 2 / (B i - A i)
        ≤ ((max (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ρ / (4 * (k + 1))) 0) ^ 2
            + 2 * (ρ / (4 * (k + 1))) * ‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖) / (B i - A i) :=
          div_le_div_of_nonneg_right key hwi.le
      _ = _ := by rw [add_div]; ring
  calc ∑ i, ‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ ^ 2 / (B i - A i)
      ≤ ∑ i, ((max (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ρ / (4 * (k + 1))) 0) ^ 2 / (B i - A i)
          + 2 * (ρ / (4 * (k + 1))) * (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ / (B i - A i))) :=
        Finset.sum_le_sum fun i _ => hsplit i
    _ = (∑ i, (max (‖f ⟨B i, y⟩ - f ⟨A i, y⟩‖ - ρ / (4 * (k + 1))) 0) ^ 2 / (B i - A i))
          + 2 * (ρ / (4 * (k + 1))) * k := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hkdef]
    _ ≤ K * (2 * deriv (imageAreaProfileY f α β σ) y + ρ / (2 * K))
          + 2 * (ρ / (4 * (k + 1))) * k := by linarith
    _ ≤ 2 * K * deriv (imageAreaProfileY f α β σ) y + ρ := by
        have hKne : K ≠ 0 := hK0.ne'
        have e0 : K * (2 * deriv (imageAreaProfileY f α β σ) y + ρ / (2 * K))
            = 2 * K * deriv (imageAreaProfileY f α β σ) y + ρ / 2 := by
          field_simp
        have e2 : 2 * (ρ / (4 * (k + 1))) * k ≤ ρ / 2 := by
          rw [show 2 * (ρ / (4 * (k + 1))) * k = ρ * (2 * k) / (4 * (k + 1)) by ring,
            div_le_iff₀ (by linarith : (0 : ℝ) < 4 * (k + 1))]
          nlinarith
        linarith

/-- **Master per-height Rengel sum (vertical slices).** Mirror of
`qc_master_sum_sq_div_le_horizontal`: at an abscissa `x > α` where the vertical image-area
profile of the window `[σ,τ]` is differentiable, every ordered contact-allowed family of
intervals `[S i, T i] ⊆ [σ,τ]` obeys
`∑ i, ‖f ⟨x, T i⟩ − f ⟨x, S i⟩‖²/(T i − S i) ≤ 2K · Ψ′(x)`.

*Proof sketch.* Transpose every step of the horizontal proof: shrunken rectangles
`[x, x+δ] × [S i + η, T i − η]`, the *separating* image family and the vertical strip
increment bound (`AxisRectModulusBound.vertical_strip_sep_sq_le`) in place of the crossing one —
its edges are the horizontal segments `[x, x+δ] × {S i + η}` and `[x, x+δ] × {T i − η}`,
whose image points are within `ε/2` of the corner images `f ⟨x, S i⟩`, `f ⟨x, T i⟩` — and
the vertical two-sided profile bound `imageArea_strip_le_profileX_diff`. No step uses
anything not symmetric under the transposition. -/
theorem qc_master_sum_sq_div_le_vertical {f : ℂ → ℂ} {K : ℝ} (hf : AxisRectModulusBound f K)
    {α σ τ x : ℝ} (hαx : α < x)
    (hΨ : DifferentiableAt ℝ (imageAreaProfileX f α σ τ) x)
    {m : ℕ} {S T : Fin m → ℝ}
    (hST : ∀ i, S i < T i) (hord : ∀ i j : Fin m, i < j → T i ≤ S j)
    (hmem : ∀ i, σ ≤ S i ∧ T i ≤ τ) :
    ∑ i, ‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ ^ 2 / (T i - S i)
      ≤ 2 * K * deriv (imageAreaProfileX f α σ τ) x := by
  have hcont : Continuous f := hf.2.1.continuous
  have hinj : Function.Injective f := hf.2.1.injective
  have hK1 : 1 ≤ K := hf.1
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hD0 : 0 ≤ deriv (imageAreaProfileX f α σ τ) x :=
    (monotone_imageAreaProfileX hcont α σ τ).deriv_nonneg
  -- the empty family is trivial
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact mul_nonneg (mul_nonneg (by norm_num) hK0.le) hD0
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  -- distance between explicit complex points
  have hdist_mk : ∀ a b u v : ℝ, dist (⟨a, b⟩ : ℂ) ⟨u, v⟩ ≤ |a - u| + |b - v| := by
    intro a b u v
    calc dist (⟨a, b⟩ : ℂ) ⟨u, v⟩
        ≤ dist (⟨a, b⟩ : ℂ) ⟨u, b⟩ + dist (⟨u, b⟩ : ℂ) ⟨u, v⟩ := dist_triangle _ _ _
      _ = |a - u| + |b - v| := by
          have e1 : dist (⟨a, b⟩ : ℂ) ⟨u, b⟩ = |a - u| :=
            (Complex.dist_of_im_eq
              (show (⟨a, b⟩ : ℂ).im = (⟨u, b⟩ : ℂ).im from rfl)).trans (Real.dist_eq a u)
          have e2 : dist (⟨u, b⟩ : ℂ) ⟨u, v⟩ = |b - v| :=
            (Complex.dist_of_re_eq
              (show (⟨u, b⟩ : ℂ).re = (⟨u, v⟩ : ℂ).re from rfl)).trans (Real.dist_eq b v)
          rw [e1, e2]
  -- a shortest interval
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin m => T i - S i) Finset.univ_nonempty
  -- ★: the shrunken-chord estimate, for every positive `ε` (chord shrink) and `ε'`
  -- (derivative slack)
  have star : ∀ ε : ℝ, 0 < ε → ∀ ε' : ℝ, 0 < ε' →
      ∑ i, (max (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ε) 0) ^ 2 / (T i - S i)
        ≤ K * (2 * deriv (imageAreaProfileX f α σ τ) x + ε') := by
    intro ε hε ε' hε'
    -- 1. modulus of continuity on the compact window
    have hUC : UniformContinuousOn f (axisRect x (x + 1) σ τ) :=
      (isCompact_axisRect x (x + 1) σ τ).uniformContinuousOn_of_continuous
        hcont.continuousOn
    obtain ⟨θ, hθpos, hθ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) (half_pos hε)
    -- 2. two-sided derivative window
    obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        imageAreaProfileX f α σ τ (x + δ) - imageAreaProfileX f α σ τ (x - δ)
          ≤ (2 * deriv (imageAreaProfileX f α σ τ) x + ε') * δ := by
      have hslope : Filter.Tendsto (slope (imageAreaProfileX f α σ τ) x)
          (nhdsWithin x {x}ᶜ) (nhds (deriv (imageAreaProfileX f α σ τ) x)) :=
        hasDerivAt_iff_tendsto_slope.mp hΨ.hasDerivAt
      have hev : ∀ᶠ v in nhdsWithin x {x}ᶜ,
          dist (slope (imageAreaProfileX f α σ τ) x v)
            (deriv (imageAreaProfileX f α σ τ) x) < ε' / 2 :=
        Metric.tendsto_nhds.mp hslope (ε' / 2) (half_pos hε')
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
      obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hev
      refine ⟨δ₀, hδ₀pos, fun δ hδp hδlt => ?_⟩
      have hplus : dist (slope (imageAreaProfileX f α σ τ) x (x + δ))
          (deriv (imageAreaProfileX f α σ τ) x) < ε' / 2 := by
        refine hδ₀ ?_ ?_
        · rw [Real.dist_eq, show x + δ - x = δ by ring, abs_of_pos hδp]; exact hδlt
        · exact Set.mem_compl_singleton_iff.mpr (ne_of_gt (by linarith))
      have hminus : dist (slope (imageAreaProfileX f α σ τ) x (x - δ))
          (deriv (imageAreaProfileX f α σ τ) x) < ε' / 2 := by
        refine hδ₀ ?_ ?_
        · rw [Real.dist_eq, show x - δ - x = -δ by ring, abs_neg, abs_of_pos hδp]
          exact hδlt
        · exact Set.mem_compl_singleton_iff.mpr (ne_of_lt (by linarith))
      have hsplus : (imageAreaProfileX f α σ τ (x + δ) - imageAreaProfileX f α σ τ x) / δ
          < deriv (imageAreaProfileX f α σ τ) x + ε' / 2 := by
        rw [Real.dist_eq, abs_sub_lt_iff] at hplus
        have h2 := hplus.1
        rwa [slope_def_field, show x + δ - x = δ by ring, sub_lt_iff_lt_add'] at h2
      have hsminus : (imageAreaProfileX f α σ τ x - imageAreaProfileX f α σ τ (x - δ)) / δ
          < deriv (imageAreaProfileX f α σ τ) x + ε' / 2 := by
        rw [Real.dist_eq, abs_sub_lt_iff] at hminus
        have h2 := hminus.1
        rwa [slope_def_field, show x - δ - x = -δ by ring, div_neg, ← neg_div, neg_sub,
          sub_lt_iff_lt_add'] at h2
      have eplus := (div_lt_iff₀ hδp).mp hsplus
      have eminus := (div_lt_iff₀ hδp).mp hsminus
      nlinarith [eplus, eminus]
    -- 3. choice of the scale
    set M : ℝ := min (min δ₀ θ) (min (T i₀ - S i₀) (min (x - α) 1)) with hM
    have hMδ₀ : M ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
    have hMθ : M ≤ θ := (min_le_left _ _).trans (min_le_right _ _)
    have hMw : M ≤ T i₀ - S i₀ := (min_le_right _ _).trans (min_le_left _ _)
    have hMxα : M ≤ x - α :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hM1 : M ≤ 1 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hMpos : 0 < M := by
      refine lt_min (lt_min hδ₀pos hθpos)
        (lt_min (sub_pos.mpr (hST i₀)) (lt_min (by linarith) one_pos))
    set δ : ℝ := M / 4 with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; linarith
    have hδδ₀ : δ < δ₀ := by rw [hδdef]; linarith
    have h2δθ : 2 * δ < θ := by rw [hδdef]; linarith
    have h2δw : ∀ i : Fin m, 2 * δ < T i - S i := fun i => by
      rw [hδdef]
      have := hi₀ i (Finset.mem_univ i)
      linarith
    have hαδ : α ≤ x - δ := by rw [hδdef]; linarith
    have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
    -- 4. oscillation control at scale `δ` inside the window
    have hosc : ∀ x₁ x₂ v₁ v₂ : ℝ, x ≤ x₁ → x₁ ≤ x + 1 → x ≤ x₂ → x₂ ≤ x + 1 →
        σ ≤ v₁ → v₁ ≤ τ → σ ≤ v₂ → v₂ ≤ τ →
        |x₁ - x₂| ≤ δ → |v₁ - v₂| ≤ δ →
        dist (f ⟨x₁, v₁⟩) (f ⟨x₂, v₂⟩) ≤ ε / 2 := by
      intro x₁ x₂ v₁ v₂ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      have hd : dist (⟨x₁, v₁⟩ : ℂ) ⟨x₂, v₂⟩ < θ :=
        lt_of_le_of_lt (hdist_mk x₁ v₁ x₂ v₂) (by linarith)
      exact le_of_lt (hθ _ ⟨⟨h1, h2⟩, h5, h6⟩ _ ⟨⟨h3, h4⟩, h7, h8⟩ hd)
    -- 5. volumes of the shrunken-rectangle images
    have hbig_ne : volume (f '' axisRect x (x + δ) σ τ) ≠ ⊤ :=
      (((isCompact_axisRect x (x + δ) σ τ).image hcont).measure_lt_top).ne
    have hfin : ∀ i : Fin m,
        volume (f '' axisRect x (x + δ) (S i + δ) (T i - δ)) ≠ ⊤ := fun i =>
      (((isCompact_axisRect x (x + δ) (S i + δ) (T i - δ)).image hcont).measure_lt_top).ne
    have hRsubδ : ∀ i : Fin m,
        axisRect x (x + δ) (S i + δ) (T i - δ) ⊆ axisRect x (x + δ) σ τ := by
      intro i z hz
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
      exact ⟨⟨h1, h2⟩, by linarith [(hmem i).1], by linarith [(hmem i).2]⟩
    -- 6. pairwise disjointness of the shrunken rectangles and their images
    have hRdisj : ∀ i j : Fin m, i ≠ j →
        Disjoint (axisRect x (x + δ) (S i + δ) (T i - δ))
          (axisRect x (x + δ) (S j + δ) (T j - δ)) := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · rw [Set.disjoint_left]
        intro z hzi hzj
        have h1 : z.im ≤ T i - δ := hzi.2.2
        have h2 : S j + δ ≤ z.im := hzj.2.1
        have h3 : T i ≤ S j := hord i j hlt
        linarith
      · rw [Set.disjoint_left]
        intro z hzi hzj
        have h1 : z.im ≤ T j - δ := hzj.2.2
        have h2 : S i + δ ≤ z.im := hzi.2.1
        have h3 : T j ≤ S i := hord j i hlt
        linarith
    -- 7. the disjoint sum of image areas is below the profile increment
    have hsum_vol : ∑ i : Fin m,
        (volume (f '' axisRect x (x + δ) (S i + δ) (T i - δ))).toReal
          ≤ (volume (f '' axisRect x (x + δ) σ τ)).toReal := by
      rw [← ENNReal.toReal_sum (fun i _ => hfin i)]
      refine ENNReal.toReal_mono hbig_ne ?_
      have hdisj' : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m)))
          (fun i => f '' axisRect x (x + δ) (S i + δ) (T i - δ)) := fun i _ j _ hij =>
        Set.disjoint_image_of_injective hinj (hRdisj i j hij)
      rw [← measure_biUnion_finset hdisj' fun i _ =>
        (((isCompact_axisRect x (x + δ) (S i + δ) (T i - δ)).image
          hcont).isClosed.measurableSet)]
      exact measure_mono (Set.iUnion₂_subset fun i _ => Set.image_mono (hRsubδ i))
    -- 8. per-rectangle chord–area estimate
    have hterm : ∀ i : Fin m,
        (max (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ε) 0) ^ 2 / (T i - S i)
          ≤ (K / δ) * (volume (f '' axisRect x (x + δ) (S i + δ) (T i - δ))).toReal := by
      intro i
      have hwi : 0 < T i - S i := sub_pos.mpr (hST i)
      have hKδ : 0 ≤ K / δ := (div_pos hK0 hδpos).le
      rcases le_or_gt (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖) ε with hle | hlt
      · rw [max_eq_right (by linarith), zero_pow two_ne_zero, zero_div]
        exact mul_nonneg hKδ ENNReal.toReal_nonneg
      · rw [max_eq_left (by linarith)]
        have hcd' : S i + δ < T i - δ := by linarith [h2δw i]
        have hSi := (hmem i).1
        have hTi := (hmem i).2
        have hSTi := hST i
        have h2w := h2δw i
        -- separation of the shrunken horizontal-edge images
        have hsep : ∀ τ₁ ∈ Set.Icc x (x + δ), ∀ τ₂ ∈ Set.Icc x (x + δ),
            ‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ε ≤ dist (f ⟨τ₁, S i + δ⟩) (f ⟨τ₂, T i - δ⟩) := by
          intro τ₁ hτ₁ τ₂ hτ₂
          obtain ⟨hτ₁l, hτ₁r⟩ := hτ₁
          obtain ⟨hτ₂l, hτ₂r⟩ := hτ₂
          have h1 : dist (f ⟨τ₁, S i + δ⟩) (f ⟨x, S i⟩) ≤ ε / 2 := by
            refine hosc τ₁ x (S i + δ) (S i) (by linarith) (by linarith) le_rfl
              (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) ?_ ?_
            · exact abs_le.mpr ⟨by linarith, by linarith⟩
            · exact abs_le.mpr ⟨by linarith, by linarith⟩
          have h2 : dist (f ⟨τ₂, T i - δ⟩) (f ⟨x, T i⟩) ≤ ε / 2 := by
            refine hosc τ₂ x (T i - δ) (T i) (by linarith) (by linarith) le_rfl
              (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) ?_ ?_
            · exact abs_le.mpr ⟨by linarith, by linarith⟩
            · exact abs_le.mpr ⟨by linarith, by linarith⟩
          have htri : dist (f ⟨x, T i⟩) (f ⟨x, S i⟩)
              ≤ dist (f ⟨x, T i⟩) (f ⟨τ₂, T i - δ⟩)
                + dist (f ⟨τ₂, T i - δ⟩) (f ⟨τ₁, S i + δ⟩)
                + dist (f ⟨τ₁, S i + δ⟩) (f ⟨x, S i⟩) := dist_triangle4 _ _ _ _
          have hnorm : ‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ = dist (f ⟨x, T i⟩) (f ⟨x, S i⟩) :=
            (dist_eq_norm _ _).symm
          have ec1 : dist (f ⟨x, T i⟩) (f ⟨τ₂, T i - δ⟩)
              = dist (f ⟨τ₂, T i - δ⟩) (f ⟨x, T i⟩) := dist_comm _ _
          have ec2 : dist (f ⟨τ₂, T i - δ⟩) (f ⟨τ₁, S i + δ⟩)
              = dist (f ⟨τ₁, S i + δ⟩) (f ⟨τ₂, T i - δ⟩) := dist_comm _ _
          linarith
        have hstrip := hf.vertical_strip_sep_sq_le hcd' hδpos (by linarith) hsep
        -- widen the denominator from the shrunken height to the full height
        have hmono : (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ε) ^ 2 * (δ / (K * (T i - S i)))
            ≤ (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ε) ^ 2
              * (δ / (K * ((T i - δ) - (S i + δ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact div_le_div_of_nonneg_left hδpos.le
            (mul_pos hK0 (by linarith)) (mul_le_mul_of_nonneg_left (by linarith) hK0.le)
        have hchain := hmono.trans hstrip
        have hKne : K ≠ 0 := hK0.ne'
        have hδne : δ ≠ 0 := hδpos.ne'
        have hwne : T i - S i ≠ 0 := hwi.ne'
        calc (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ε) ^ 2 / (T i - S i)
            = (K / δ) * ((‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ε) ^ 2
                * (δ / (K * (T i - S i)))) := by
              field_simp
          _ ≤ (K / δ)
                * (volume (f '' axisRect x (x + δ) (S i + δ) (T i - δ))).toReal :=
              mul_le_mul_of_nonneg_left hchain hKδ
    -- 9. sum, compare with the profile increment, divide by `δ/K`
    have hδne : δ ≠ 0 := hδpos.ne'
    calc ∑ i, (max (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ε) 0) ^ 2 / (T i - S i)
        ≤ ∑ i, (K / δ)
            * (volume (f '' axisRect x (x + δ) (S i + δ) (T i - δ))).toReal :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (K / δ) * ∑ i,
            (volume (f '' axisRect x (x + δ) (S i + δ) (T i - δ))).toReal := by
          rw [Finset.mul_sum]
      _ ≤ (K / δ) * ((2 * deriv (imageAreaProfileX f α σ τ) x + ε') * δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_pos hK0 hδpos).le
          calc ∑ i, (volume (f '' axisRect x (x + δ) (S i + δ) (T i - δ))).toReal
              ≤ (volume (f '' axisRect x (x + δ) σ τ)).toReal := hsum_vol
            _ ≤ imageAreaProfileX f α σ τ (x + δ) - imageAreaProfileX f α σ τ (x - δ) :=
                imageArea_strip_le_profileX_diff hcont hinj hδpos hαδ
            _ ≤ (2 * deriv (imageAreaProfileX f α σ τ) x + ε') * δ := hδ₀ δ hδpos hδδ₀
      _ = K * (2 * deriv (imageAreaProfileX f α σ τ) x + ε') := by
          field_simp
  -- the `ε, ε' → 0` reduction
  refine le_of_forall_pos_le_add fun ρ hρ => ?_
  have hknn : (0 : ℝ) ≤ ∑ i, ‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ / (T i - S i) :=
    Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (sub_pos.mpr (hST i)).le
  set k : ℝ := ∑ i, ‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ / (T i - S i) with hkdef
  have hεp : 0 < ρ / (4 * (k + 1)) := div_pos hρ (by linarith)
  have hε'p : 0 < ρ / (2 * K) := div_pos hρ (by linarith)
  have hstar := star _ hεp _ hε'p
  have hsplit : ∀ i : Fin m,
      ‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ ^ 2 / (T i - S i)
        ≤ (max (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ρ / (4 * (k + 1))) 0) ^ 2 / (T i - S i)
          + 2 * (ρ / (4 * (k + 1))) * (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ / (T i - S i)) := by
    intro i
    have hwi : 0 < T i - S i := sub_pos.mpr (hST i)
    have hr : (0 : ℝ) ≤ ‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ := norm_nonneg _
    have key : ‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ ^ 2
        ≤ (max (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ρ / (4 * (k + 1))) 0) ^ 2
          + 2 * (ρ / (4 * (k + 1))) * ‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ := by
      rcases le_or_gt (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖) (ρ / (4 * (k + 1))) with h | h
      · rw [max_eq_right (by linarith)]
        nlinarith [mul_nonneg hr (sub_nonneg.mpr h), mul_nonneg hεp.le hr]
      · rw [max_eq_left (by linarith)]
        nlinarith [sq_nonneg (ρ / (4 * (k + 1)))]
    calc ‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ ^ 2 / (T i - S i)
        ≤ ((max (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ρ / (4 * (k + 1))) 0) ^ 2
            + 2 * (ρ / (4 * (k + 1))) * ‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖) / (T i - S i) :=
          div_le_div_of_nonneg_right key hwi.le
      _ = _ := by rw [add_div]; ring
  calc ∑ i, ‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ ^ 2 / (T i - S i)
      ≤ ∑ i, ((max (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ρ / (4 * (k + 1))) 0) ^ 2 / (T i - S i)
          + 2 * (ρ / (4 * (k + 1))) * (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ / (T i - S i))) :=
        Finset.sum_le_sum fun i _ => hsplit i
    _ = (∑ i, (max (‖f ⟨x, T i⟩ - f ⟨x, S i⟩‖ - ρ / (4 * (k + 1))) 0) ^ 2 / (T i - S i))
          + 2 * (ρ / (4 * (k + 1))) * k := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hkdef]
    _ ≤ K * (2 * deriv (imageAreaProfileX f α σ τ) x + ρ / (2 * K))
          + 2 * (ρ / (4 * (k + 1))) * k := by linarith
    _ ≤ 2 * K * deriv (imageAreaProfileX f α σ τ) x + ρ := by
        have hKne : K ≠ 0 := hK0.ne'
        have e0 : K * (2 * deriv (imageAreaProfileX f α σ τ) x + ρ / (2 * K))
            = 2 * K * deriv (imageAreaProfileX f α σ τ) x + ρ / 2 := by
          field_simp
        have e2 : 2 * (ρ / (4 * (k + 1))) * k ≤ ρ / 2 := by
          rw [show 2 * (ρ / (4 * (k + 1))) * k = ρ * (2 * k) / (4 * (k + 1)) by ring,
            div_le_iff₀ (by linarith : (0 : ℝ) < 4 * (k + 1))]
          nlinarith
        linarith

/-- **One-sided master family estimate at a good height (horizontal slices; disjoint closed
intervals).** Let `y ≥ σ` be a height at which the horizontal image-area profile is
differentiable *and* whose segment `[α,β] × {y}` has null image. For every finite family of
pairwise disjoint closed intervals `[c i, d i] ⊆ [α,β]`,
`∑ i, dist (f ⟨c i, y⟩) (f ⟨d i, y⟩)²/(d i − c i) ≤ K · Φ′(y)`.

Compared with the contact-allowed estimate this version needs no shrinking (the closed
intervals are already disjoint) and achieves the constant `K`, at the price of the
null-segment hypothesis, which allows a *one-sided* comparison with the profile. One good
`y` works simultaneously for **all** finite families — no countability over families is
needed, only over the window exhaustion.

*Proof sketch.* Fix `ε > 0`. Continuity of `τ ↦ f ⟨c i, τ⟩` and `τ ↦ f ⟨d i, τ⟩` at `y`
gives `h₀ > 0` with oscillation `≤ ε/2` on `[y, y+h₀]` for all (finitely many) `i`; the
triangle inequality yields the edge separation `Dᵢ − ε` for the strip
`[c i, d i] × [y, y+h]`, `h ≤ h₀` (indices with `Dᵢ ≤ ε` contribute `0`). For such `h`:
1. the strip increment bound (`AxisRectModulusBound.horizontal_strip_sep_sq_le`) gives
   `(max (Dᵢ − ε) 0)² · h/(K·wᵢ) ≤ area (f '' Sᵢ)` per strip;
2. the strips are pairwise disjoint, so by injectivity their compact images are pairwise
   disjoint and `∑ᵢ area (f '' Sᵢ) ≤ area (f '' ([α,β] × [y, y+h]))`
   (`measure_biUnion_finset`, monotonicity);
3. the one-sided profile bound (`imageArea_strip_le_profileY_diff_right`, using the null
   segment) dominates the right-hand side by `Φ(y+h) − Φ(y)`.
Divide by `h` and let `h → 0⁺`: the left side is `h`-free and the right difference quotient
tends to `Φ′(y)` (`hasDerivAt_iff_tendsto_slope` restricted to `𝓝[>] y`, `le_of_tendsto`).
Then let `ε → 0` (finitely many terms, each continuous in `ε`).
-/
theorem AxisRectModulusBound.horizontal_family_sq_sum_le {f : ℂ → ℂ} {K : ℝ}
    (hf : AxisRectModulusBound f K) {α β σ y : ℝ} (hσy : σ ≤ y)
    (hdiff : DifferentiableAt ℝ (imageAreaProfileY f α β σ) y)
    (hseg : volume (f '' axisRect α β y y) = 0)
    {N : ℕ} {c d : Fin N → ℝ} (hcd : ∀ i, c i < d i)
    (hsub : ∀ i, Set.Icc (c i) (d i) ⊆ Set.Icc α β)
    (hdisj : Pairwise (Function.onFun Disjoint fun i => Set.Icc (c i) (d i))) :
    ∑ i, dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) ^ 2 / (d i - c i)
      ≤ K * deriv (imageAreaProfileY f α β σ) y := by
  have hcont : Continuous f := hf.2.1.continuous
  have hinj : Function.Injective f := hf.2.1.injective
  have hK1 : 1 ≤ K := hf.1
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hD0 : 0 ≤ deriv (imageAreaProfileY f α β σ) y :=
    (monotone_imageAreaProfileY hcont α β σ).deriv_nonneg
  -- the empty family is trivial
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact mul_nonneg hK0.le hD0
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hwd : ∀ i : Fin N, α ≤ c i ∧ d i ≤ β := fun i =>
    ⟨(hsub i ⟨le_refl _, (hcd i).le⟩).1, (hsub i ⟨(hcd i).le, le_refl _⟩).2⟩
  -- ★: the shrunken-chord estimate for every positive `ε`
  have star : ∀ ε : ℝ, 0 < ε →
      ∑ i, (max (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) - ε) 0) ^ 2 / (d i - c i)
        ≤ K * deriv (imageAreaProfileY f α β σ) y := by
    intro ε hε
    -- modulus of continuity on the compact window
    have hUC : UniformContinuousOn f (axisRect α β y (y + 1)) :=
      (isCompact_axisRect α β y (y + 1)).uniformContinuousOn_of_continuous
        hcont.continuousOn
    obtain ⟨θ, hθpos, hθ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) (half_pos hε)
    -- the fixed-height difference-quotient estimate
    have key : ∀ h : ℝ, 0 < h → h ≤ min (θ / 2) 1 →
        ∑ i, (max (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) - ε) 0) ^ 2 / (d i - c i)
          ≤ K * ((imageAreaProfileY f α β σ (y + h)
              - imageAreaProfileY f α β σ y) / h) := by
      intro h hh hhle
      have hh1 : h ≤ 1 := hhle.trans (min_le_right _ _)
      have hhθ : h < θ := lt_of_le_of_lt (hhle.trans (min_le_left _ _)) (by linarith)
      -- oscillation along the degenerating vertical edges
      have hosc : ∀ x' τ' : ℝ, α ≤ x' → x' ≤ β → y ≤ τ' → τ' ≤ y + h →
          dist (f ⟨x', τ'⟩) (f ⟨x', y⟩) ≤ ε / 2 := by
        intro x' τ' h1 h2 h3 h4
        have hd : dist (⟨x', τ'⟩ : ℂ) ⟨x', y⟩ < θ := by
          have e2 : dist (⟨x', τ'⟩ : ℂ) ⟨x', y⟩ = |τ' - y| :=
            (Complex.dist_of_re_eq
              (show (⟨x', τ'⟩ : ℂ).re = (⟨x', y⟩ : ℂ).re from rfl)).trans
              (Real.dist_eq τ' y)
          rw [e2, abs_of_nonneg (by linarith)]
          linarith
        exact le_of_lt (hθ _ ⟨⟨h1, h2⟩, h3, by linarith⟩
          _ ⟨⟨h1, h2⟩, le_refl y, by linarith⟩ hd)
      -- finiteness of the strip image volumes
      have hbig_ne : volume (f '' axisRect α β y (y + h)) ≠ ⊤ :=
        (((isCompact_axisRect α β y (y + h)).image hcont).measure_lt_top).ne
      have hfin : ∀ i : Fin N,
          volume (f '' axisRect (c i) (d i) y (y + h)) ≠ ⊤ := fun i =>
        (((isCompact_axisRect (c i) (d i) y (y + h)).image hcont).measure_lt_top).ne
      have hRsub : ∀ i : Fin N,
          axisRect (c i) (d i) y (y + h) ⊆ axisRect α β y (y + h) := by
        intro i z hz
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
        exact ⟨⟨le_trans (hwd i).1 h1, le_trans h2 (hwd i).2⟩, h3, h4⟩
      -- pairwise disjointness of the closed strips and their images
      have hRdisj : ∀ i j : Fin N, i ≠ j →
          Disjoint (axisRect (c i) (d i) y (y + h))
            (axisRect (c j) (d j) y (y + h)) := by
        intro i j hij
        rw [Set.disjoint_left]
        intro z hzi hzj
        exact Set.disjoint_left.mp (hdisj hij) ⟨hzi.1.1, hzi.1.2⟩ ⟨hzj.1.1, hzj.1.2⟩
      -- the disjoint sum of the image areas
      have hsum_vol : ∑ i : Fin N,
          (volume (f '' axisRect (c i) (d i) y (y + h))).toReal
            ≤ (volume (f '' axisRect α β y (y + h))).toReal := by
        rw [← ENNReal.toReal_sum (fun i _ => hfin i)]
        refine ENNReal.toReal_mono hbig_ne ?_
        have hdisj' : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)))
            (fun i => f '' axisRect (c i) (d i) y (y + h)) := fun i _ j _ hij =>
          Set.disjoint_image_of_injective hinj (hRdisj i j hij)
        rw [← measure_biUnion_finset hdisj' fun i _ =>
          (((isCompact_axisRect (c i) (d i) y (y + h)).image
            hcont).isClosed.measurableSet)]
        exact measure_mono (Set.iUnion₂_subset fun i _ => Set.image_mono (hRsub i))
      -- per-strip chord–area estimate
      have hterm : ∀ i : Fin N,
          (max (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) - ε) 0) ^ 2 / (d i - c i)
            ≤ (K / h) * (volume (f '' axisRect (c i) (d i) y (y + h))).toReal := by
        intro i
        have hwi : 0 < d i - c i := sub_pos.mpr (hcd i)
        have hKh : 0 ≤ K / h := (div_pos hK0 hh).le
        rcases le_or_gt (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩)) ε with hle | hlt
        · rw [max_eq_right (by linarith), zero_pow two_ne_zero, zero_div]
          exact mul_nonneg hKh ENNReal.toReal_nonneg
        · rw [max_eq_left (by linarith)]
          have hsep : ∀ τ₁ ∈ Set.Icc y (y + h), ∀ τ₂ ∈ Set.Icc y (y + h),
              dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) - ε
                ≤ dist (f ⟨c i, τ₁⟩) (f ⟨d i, τ₂⟩) := by
            intro τ₁ hτ₁ τ₂ hτ₂
            obtain ⟨hτ₁l, hτ₁r⟩ := hτ₁
            obtain ⟨hτ₂l, hτ₂r⟩ := hτ₂
            have h1 : dist (f ⟨c i, τ₁⟩) (f ⟨c i, y⟩) ≤ ε / 2 :=
              hosc (c i) τ₁ (hwd i).1 (le_trans (hcd i).le (hwd i).2) hτ₁l hτ₁r
            have h2 : dist (f ⟨d i, τ₂⟩) (f ⟨d i, y⟩) ≤ ε / 2 :=
              hosc (d i) τ₂ (le_trans (hwd i).1 (hcd i).le) (hwd i).2 hτ₂l hτ₂r
            have htri : dist (f ⟨c i, y⟩) (f ⟨d i, y⟩)
                ≤ dist (f ⟨c i, y⟩) (f ⟨c i, τ₁⟩) + dist (f ⟨c i, τ₁⟩) (f ⟨d i, τ₂⟩)
                  + dist (f ⟨d i, τ₂⟩) (f ⟨d i, y⟩) := dist_triangle4 _ _ _ _
            have ec1 : dist (f ⟨c i, y⟩) (f ⟨c i, τ₁⟩)
                = dist (f ⟨c i, τ₁⟩) (f ⟨c i, y⟩) := dist_comm _ _
            linarith
          have hstrip := hf.horizontal_strip_sep_sq_le (hcd i) hh (by linarith) hsep
          have hKne : K ≠ 0 := hK0.ne'
          have hhne : h ≠ 0 := hh.ne'
          have hwne : d i - c i ≠ 0 := hwi.ne'
          calc (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) - ε) ^ 2 / (d i - c i)
              = (K / h) * ((dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) - ε) ^ 2
                  * (h / (K * (d i - c i)))) := by field_simp
            _ ≤ (K / h) * (volume (f '' axisRect (c i) (d i) y (y + h))).toReal :=
                mul_le_mul_of_nonneg_left hstrip hKh
      calc ∑ i, (max (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) - ε) 0) ^ 2 / (d i - c i)
          ≤ ∑ i, (K / h) * (volume (f '' axisRect (c i) (d i) y (y + h))).toReal :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = (K / h) * ∑ i,
              (volume (f '' axisRect (c i) (d i) y (y + h))).toReal := by
            rw [Finset.mul_sum]
        _ ≤ (K / h) * (imageAreaProfileY f α β σ (y + h)
              - imageAreaProfileY f α β σ y) := by
            refine mul_le_mul_of_nonneg_left ?_ (div_pos hK0 hh).le
            exact hsum_vol.trans
              (imageArea_strip_le_profileY_diff_right hcont hinj hh hσy hseg)
        _ = K * ((imageAreaProfileY f α β σ (y + h)
              - imageAreaProfileY f α β σ y) / h) := by ring
    -- let `h → 0⁺` along the right difference quotient
    have hh₀pos : (0 : ℝ) < min (θ / 2) 1 := lt_min (by linarith) one_pos
    have hslope : Filter.Tendsto (fun v => K * slope (imageAreaProfileY f α β σ) y v)
        (nhdsWithin y (Set.Ioi y)) (nhds (K * deriv (imageAreaProfileY f α β σ) y)) :=
      Filter.Tendsto.const_mul K
        ((hasDerivAt_iff_tendsto_slope.mp hdiff.hasDerivAt).mono_left
          (nhdsWithin_mono y fun v hv => Set.mem_compl_singleton_iff.mpr (ne_of_gt hv)))
    refine ge_of_tendsto hslope ?_
    filter_upwards [Ioc_mem_nhdsGT (by linarith : y < y + min (θ / 2) 1)] with v hv
    have hkey := key (v - y) (by linarith [hv.1]) (by linarith [hv.2])
    rw [show y + (v - y) = v by ring] at hkey
    rw [slope_def_field]
    exact hkey
  -- the `ε → 0` reduction
  refine le_of_forall_pos_le_add fun ρ hρ => ?_
  have hknn : (0 : ℝ) ≤ ∑ i, dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) / (d i - c i) :=
    Finset.sum_nonneg fun i _ => div_nonneg dist_nonneg (sub_pos.mpr (hcd i)).le
  set k : ℝ := ∑ i, dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) / (d i - c i) with hkdef
  have hεp : 0 < ρ / (2 * (k + 1)) := div_pos hρ (by linarith)
  have hstar := star _ hεp
  have hsplit : ∀ i : Fin N,
      dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) ^ 2 / (d i - c i)
        ≤ (max (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) - ρ / (2 * (k + 1))) 0) ^ 2 / (d i - c i)
          + 2 * (ρ / (2 * (k + 1)))
            * (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) / (d i - c i)) := by
    intro i
    have hwi : 0 < d i - c i := sub_pos.mpr (hcd i)
    have hr : (0 : ℝ) ≤ dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) := dist_nonneg
    have key : dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) ^ 2
        ≤ (max (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) - ρ / (2 * (k + 1))) 0) ^ 2
          + 2 * (ρ / (2 * (k + 1))) * dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) := by
      rcases le_or_gt (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩)) (ρ / (2 * (k + 1))) with h | h
      · rw [max_eq_right (by linarith)]
        nlinarith [mul_nonneg hr (sub_nonneg.mpr h), mul_nonneg hεp.le hr]
      · rw [max_eq_left (by linarith)]
        nlinarith [sq_nonneg (ρ / (2 * (k + 1)))]
    calc dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) ^ 2 / (d i - c i)
        ≤ ((max (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) - ρ / (2 * (k + 1))) 0) ^ 2
            + 2 * (ρ / (2 * (k + 1))) * dist (f ⟨c i, y⟩) (f ⟨d i, y⟩)) / (d i - c i) :=
          div_le_div_of_nonneg_right key hwi.le
      _ = _ := by rw [add_div]; ring
  calc ∑ i, dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) ^ 2 / (d i - c i)
      ≤ ∑ i, ((max (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) - ρ / (2 * (k + 1))) 0) ^ 2
            / (d i - c i)
          + 2 * (ρ / (2 * (k + 1)))
            * (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) / (d i - c i))) :=
        Finset.sum_le_sum fun i _ => hsplit i
    _ = (∑ i, (max (dist (f ⟨c i, y⟩) (f ⟨d i, y⟩) - ρ / (2 * (k + 1))) 0) ^ 2
            / (d i - c i))
          + 2 * (ρ / (2 * (k + 1))) * k := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hkdef]
    _ ≤ K * deriv (imageAreaProfileY f α β σ) y + 2 * (ρ / (2 * (k + 1))) * k := by
        linarith
    _ ≤ K * deriv (imageAreaProfileY f α β σ) y + ρ := by
        have e2 : 2 * (ρ / (2 * (k + 1))) * k ≤ ρ := by
          rw [show 2 * (ρ / (2 * (k + 1))) * k = ρ * (2 * k) / (2 * (k + 1)) by ring,
            div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (k + 1))]
          nlinarith
        linarith

/-- **One-sided master family estimate at a good abscissa (vertical slices).** Mirror of
`AxisRectModulusBound.horizontal_family_sq_sum_le`: at `x ≥ α` where the vertical image-area
profile is differentiable and the vertical segment `{x} × [σ,τ]` has null image, every
family of pairwise disjoint closed intervals `[c i, d i] ⊆ [σ,τ]` obeys
`∑ i, dist (f ⟨x, c i⟩) (f ⟨x, d i⟩)²/(d i − c i) ≤ K · Ψ′(x)`.

*Proof sketch.* Transpose the horizontal proof: strips `[x, x+h] × [c i, d i]`, the
vertical strip increment bound (`AxisRectModulusBound.vertical_strip_sep_sq_le`), and the
one-sided vertical profile bound (`imageArea_strip_le_profileX_diff_right`) with the null
vertical segment. -/
theorem AxisRectModulusBound.vertical_family_sq_sum_le {f : ℂ → ℂ} {K : ℝ}
    (hf : AxisRectModulusBound f K) {α σ τ x : ℝ} (hαx : α ≤ x)
    (hdiff : DifferentiableAt ℝ (imageAreaProfileX f α σ τ) x)
    (hseg : volume (f '' axisRect x x σ τ) = 0)
    {N : ℕ} {c d : Fin N → ℝ} (hcd : ∀ i, c i < d i)
    (hsub : ∀ i, Set.Icc (c i) (d i) ⊆ Set.Icc σ τ)
    (hdisj : Pairwise (Function.onFun Disjoint fun i => Set.Icc (c i) (d i))) :
    ∑ i, dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) ^ 2 / (d i - c i)
      ≤ K * deriv (imageAreaProfileX f α σ τ) x := by
  have hcont : Continuous f := hf.2.1.continuous
  have hinj : Function.Injective f := hf.2.1.injective
  have hK1 : 1 ≤ K := hf.1
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hD0 : 0 ≤ deriv (imageAreaProfileX f α σ τ) x :=
    (monotone_imageAreaProfileX hcont α σ τ).deriv_nonneg
  -- the empty family is trivial
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact mul_nonneg hK0.le hD0
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hwd : ∀ i : Fin N, σ ≤ c i ∧ d i ≤ τ := fun i =>
    ⟨(hsub i ⟨le_refl _, (hcd i).le⟩).1, (hsub i ⟨(hcd i).le, le_refl _⟩).2⟩
  -- ★: the shrunken-chord estimate for every positive `ε`
  have star : ∀ ε : ℝ, 0 < ε →
      ∑ i, (max (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) - ε) 0) ^ 2 / (d i - c i)
        ≤ K * deriv (imageAreaProfileX f α σ τ) x := by
    intro ε hε
    -- modulus of continuity on the compact window
    have hUC : UniformContinuousOn f (axisRect x (x + 1) σ τ) :=
      (isCompact_axisRect x (x + 1) σ τ).uniformContinuousOn_of_continuous
        hcont.continuousOn
    obtain ⟨θ, hθpos, hθ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) (half_pos hε)
    -- the fixed-width difference-quotient estimate
    have key : ∀ h : ℝ, 0 < h → h ≤ min (θ / 2) 1 →
        ∑ i, (max (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) - ε) 0) ^ 2 / (d i - c i)
          ≤ K * ((imageAreaProfileX f α σ τ (x + h)
              - imageAreaProfileX f α σ τ x) / h) := by
      intro h hh hhle
      have hh1 : h ≤ 1 := hhle.trans (min_le_right _ _)
      have hhθ : h < θ := lt_of_le_of_lt (hhle.trans (min_le_left _ _)) (by linarith)
      -- oscillation along the degenerating horizontal edges
      have hosc : ∀ v' τ' : ℝ, σ ≤ v' → v' ≤ τ → x ≤ τ' → τ' ≤ x + h →
          dist (f ⟨τ', v'⟩) (f ⟨x, v'⟩) ≤ ε / 2 := by
        intro v' τ' h1 h2 h3 h4
        have hd : dist (⟨τ', v'⟩ : ℂ) ⟨x, v'⟩ < θ := by
          have e2 : dist (⟨τ', v'⟩ : ℂ) ⟨x, v'⟩ = |τ' - x| :=
            (Complex.dist_of_im_eq
              (show (⟨τ', v'⟩ : ℂ).im = (⟨x, v'⟩ : ℂ).im from rfl)).trans
              (Real.dist_eq τ' x)
          rw [e2, abs_of_nonneg (by linarith)]
          linarith
        exact le_of_lt (hθ _ ⟨⟨h3, by linarith⟩, h1, h2⟩
          _ ⟨⟨le_refl x, by linarith⟩, h1, h2⟩ hd)
      -- finiteness of the strip image volumes
      have hbig_ne : volume (f '' axisRect x (x + h) σ τ) ≠ ⊤ :=
        (((isCompact_axisRect x (x + h) σ τ).image hcont).measure_lt_top).ne
      have hfin : ∀ i : Fin N,
          volume (f '' axisRect x (x + h) (c i) (d i)) ≠ ⊤ := fun i =>
        (((isCompact_axisRect x (x + h) (c i) (d i)).image hcont).measure_lt_top).ne
      have hRsub : ∀ i : Fin N,
          axisRect x (x + h) (c i) (d i) ⊆ axisRect x (x + h) σ τ := by
        intro i z hz
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
        exact ⟨⟨h1, h2⟩, le_trans (hwd i).1 h3, le_trans h4 (hwd i).2⟩
      -- pairwise disjointness of the closed strips and their images
      have hRdisj : ∀ i j : Fin N, i ≠ j →
          Disjoint (axisRect x (x + h) (c i) (d i))
            (axisRect x (x + h) (c j) (d j)) := by
        intro i j hij
        rw [Set.disjoint_left]
        intro z hzi hzj
        exact Set.disjoint_left.mp (hdisj hij) ⟨hzi.2.1, hzi.2.2⟩ ⟨hzj.2.1, hzj.2.2⟩
      -- the disjoint sum of the image areas
      have hsum_vol : ∑ i : Fin N,
          (volume (f '' axisRect x (x + h) (c i) (d i))).toReal
            ≤ (volume (f '' axisRect x (x + h) σ τ)).toReal := by
        rw [← ENNReal.toReal_sum (fun i _ => hfin i)]
        refine ENNReal.toReal_mono hbig_ne ?_
        have hdisj' : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)))
            (fun i => f '' axisRect x (x + h) (c i) (d i)) := fun i _ j _ hij =>
          Set.disjoint_image_of_injective hinj (hRdisj i j hij)
        rw [← measure_biUnion_finset hdisj' fun i _ =>
          (((isCompact_axisRect x (x + h) (c i) (d i)).image
            hcont).isClosed.measurableSet)]
        exact measure_mono (Set.iUnion₂_subset fun i _ => Set.image_mono (hRsub i))
      -- per-strip chord–area estimate
      have hterm : ∀ i : Fin N,
          (max (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) - ε) 0) ^ 2 / (d i - c i)
            ≤ (K / h) * (volume (f '' axisRect x (x + h) (c i) (d i))).toReal := by
        intro i
        have hwi : 0 < d i - c i := sub_pos.mpr (hcd i)
        have hKh : 0 ≤ K / h := (div_pos hK0 hh).le
        rcases le_or_gt (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩)) ε with hle | hlt
        · rw [max_eq_right (by linarith), zero_pow two_ne_zero, zero_div]
          exact mul_nonneg hKh ENNReal.toReal_nonneg
        · rw [max_eq_left (by linarith)]
          have hsep : ∀ τ₁ ∈ Set.Icc x (x + h), ∀ τ₂ ∈ Set.Icc x (x + h),
              dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) - ε
                ≤ dist (f ⟨τ₁, c i⟩) (f ⟨τ₂, d i⟩) := by
            intro τ₁ hτ₁ τ₂ hτ₂
            obtain ⟨hτ₁l, hτ₁r⟩ := hτ₁
            obtain ⟨hτ₂l, hτ₂r⟩ := hτ₂
            have h1 : dist (f ⟨τ₁, c i⟩) (f ⟨x, c i⟩) ≤ ε / 2 :=
              hosc (c i) τ₁ (hwd i).1 (le_trans (hcd i).le (hwd i).2) hτ₁l hτ₁r
            have h2 : dist (f ⟨τ₂, d i⟩) (f ⟨x, d i⟩) ≤ ε / 2 :=
              hosc (d i) τ₂ (le_trans (hwd i).1 (hcd i).le) (hwd i).2 hτ₂l hτ₂r
            have htri : dist (f ⟨x, c i⟩) (f ⟨x, d i⟩)
                ≤ dist (f ⟨x, c i⟩) (f ⟨τ₁, c i⟩) + dist (f ⟨τ₁, c i⟩) (f ⟨τ₂, d i⟩)
                  + dist (f ⟨τ₂, d i⟩) (f ⟨x, d i⟩) := dist_triangle4 _ _ _ _
            have ec1 : dist (f ⟨x, c i⟩) (f ⟨τ₁, c i⟩)
                = dist (f ⟨τ₁, c i⟩) (f ⟨x, c i⟩) := dist_comm _ _
            linarith
          have hstrip := hf.vertical_strip_sep_sq_le (hcd i) hh (by linarith) hsep
          have hKne : K ≠ 0 := hK0.ne'
          have hhne : h ≠ 0 := hh.ne'
          have hwne : d i - c i ≠ 0 := hwi.ne'
          calc (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) - ε) ^ 2 / (d i - c i)
              = (K / h) * ((dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) - ε) ^ 2
                  * (h / (K * (d i - c i)))) := by field_simp
            _ ≤ (K / h) * (volume (f '' axisRect x (x + h) (c i) (d i))).toReal :=
                mul_le_mul_of_nonneg_left hstrip hKh
      calc ∑ i, (max (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) - ε) 0) ^ 2 / (d i - c i)
          ≤ ∑ i, (K / h) * (volume (f '' axisRect x (x + h) (c i) (d i))).toReal :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = (K / h) * ∑ i,
              (volume (f '' axisRect x (x + h) (c i) (d i))).toReal := by
            rw [Finset.mul_sum]
        _ ≤ (K / h) * (imageAreaProfileX f α σ τ (x + h)
              - imageAreaProfileX f α σ τ x) := by
            refine mul_le_mul_of_nonneg_left ?_ (div_pos hK0 hh).le
            exact hsum_vol.trans
              (imageArea_strip_le_profileX_diff_right hcont hinj hh hαx hseg)
        _ = K * ((imageAreaProfileX f α σ τ (x + h)
              - imageAreaProfileX f α σ τ x) / h) := by ring
    -- let `h → 0⁺` along the right difference quotient
    have hh₀pos : (0 : ℝ) < min (θ / 2) 1 := lt_min (by linarith) one_pos
    have hslope : Filter.Tendsto (fun v => K * slope (imageAreaProfileX f α σ τ) x v)
        (nhdsWithin x (Set.Ioi x)) (nhds (K * deriv (imageAreaProfileX f α σ τ) x)) :=
      Filter.Tendsto.const_mul K
        ((hasDerivAt_iff_tendsto_slope.mp hdiff.hasDerivAt).mono_left
          (nhdsWithin_mono x fun v hv => Set.mem_compl_singleton_iff.mpr (ne_of_gt hv)))
    refine ge_of_tendsto hslope ?_
    filter_upwards [Ioc_mem_nhdsGT (by linarith : x < x + min (θ / 2) 1)] with v hv
    have hkey := key (v - x) (by linarith [hv.1]) (by linarith [hv.2])
    rw [show x + (v - x) = v by ring] at hkey
    rw [slope_def_field]
    exact hkey
  -- the `ε → 0` reduction
  refine le_of_forall_pos_le_add fun ρ hρ => ?_
  have hknn : (0 : ℝ) ≤ ∑ i, dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) / (d i - c i) :=
    Finset.sum_nonneg fun i _ => div_nonneg dist_nonneg (sub_pos.mpr (hcd i)).le
  set k : ℝ := ∑ i, dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) / (d i - c i) with hkdef
  have hεp : 0 < ρ / (2 * (k + 1)) := div_pos hρ (by linarith)
  have hstar := star _ hεp
  have hsplit : ∀ i : Fin N,
      dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) ^ 2 / (d i - c i)
        ≤ (max (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) - ρ / (2 * (k + 1))) 0) ^ 2 / (d i - c i)
          + 2 * (ρ / (2 * (k + 1)))
            * (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) / (d i - c i)) := by
    intro i
    have hwi : 0 < d i - c i := sub_pos.mpr (hcd i)
    have hr : (0 : ℝ) ≤ dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) := dist_nonneg
    have key : dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) ^ 2
        ≤ (max (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) - ρ / (2 * (k + 1))) 0) ^ 2
          + 2 * (ρ / (2 * (k + 1))) * dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) := by
      rcases le_or_gt (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩)) (ρ / (2 * (k + 1))) with h | h
      · rw [max_eq_right (by linarith)]
        nlinarith [mul_nonneg hr (sub_nonneg.mpr h), mul_nonneg hεp.le hr]
      · rw [max_eq_left (by linarith)]
        nlinarith [sq_nonneg (ρ / (2 * (k + 1)))]
    calc dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) ^ 2 / (d i - c i)
        ≤ ((max (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) - ρ / (2 * (k + 1))) 0) ^ 2
            + 2 * (ρ / (2 * (k + 1))) * dist (f ⟨x, c i⟩) (f ⟨x, d i⟩)) / (d i - c i) :=
          div_le_div_of_nonneg_right key hwi.le
      _ = _ := by rw [add_div]; ring
  calc ∑ i, dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) ^ 2 / (d i - c i)
      ≤ ∑ i, ((max (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) - ρ / (2 * (k + 1))) 0) ^ 2
            / (d i - c i)
          + 2 * (ρ / (2 * (k + 1)))
            * (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) / (d i - c i))) :=
        Finset.sum_le_sum fun i _ => hsplit i
    _ = (∑ i, (max (dist (f ⟨x, c i⟩) (f ⟨x, d i⟩) - ρ / (2 * (k + 1))) 0) ^ 2
            / (d i - c i))
          + 2 * (ρ / (2 * (k + 1))) * k := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hkdef]
    _ ≤ K * deriv (imageAreaProfileX f α σ τ) x + 2 * (ρ / (2 * (k + 1))) * k := by
        linarith
    _ ≤ K * deriv (imageAreaProfileX f α σ τ) x + ρ := by
        have e2 : 2 * (ρ / (2 * (k + 1))) * k ≤ ρ := by
          rw [show 2 * (ρ / (2 * (k + 1))) * k = ρ * (2 * k) / (2 * (k + 1)) by ring,
            div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (k + 1))]
          nlinarith
        linarith

end NoWanderingDomains
