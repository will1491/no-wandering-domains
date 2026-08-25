/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.MRMT.Existence
import NoWanderingDomains.QC.Calculus.Weyl
import NoWanderingDomains.QC.Calculus.Composition

/-!
# Uniqueness of normalized quasiconformal solutions

Two quasiconformal solutions of the same Beltrami equation differ by a conformal
automorphism of the plane: the transition map `f₂ ∘ f₁⁻¹` is `1`-quasiconformal
(equal coefficients cancel through the almost-everywhere chain rule), hence entire
by Weyl's lemma, hence affine by injectivity — so the two-point normalization
`f 0 = 0`, `f 1 = 1` pins the solution:

`mrmt_unique_normalized : ∃! f, IsQCAnalytic f b ∧ f 0 = 0 ∧ f 1 = 1`.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **An injective entire function is affine**: `f = a·z + c` with `a ≠ 0`. The
singularity at infinity is not essential (Casorati–Weierstrass against openness of
the image), so `f` is a polynomial, and injectivity forces degree one. -/
theorem eq_affine_of_differentiable_of_injective {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hinj : Function.Injective f) :
    ∃ a c : ℂ, a ≠ 0 ∧ f = fun z => a * z + c := by
  classical
  -- `f` is nonconstant.
  have hne : f 0 ≠ f 1 := fun h => zero_ne_one (hinj h)
  -- Open mapping theorem: `f` is an open map.
  have hopen : IsOpenMap f := by
    have hA : AnalyticOnNhd ℂ f Set.univ := fun z _ =>
      hf.differentiableOn.analyticAt Filter.univ_mem
    rcases hA.is_constant_or_isOpenMap with ⟨w, hw⟩ | h
    · exact absurd ((hw 0).trans (hw 1).symm) hne
    · exact h
  set c : ℂ := f 0 with hc_def
  -- The image of the unit ball is open, so it contains a ball `B(c, ε)`; by
  -- injectivity `f` omits this ball on `{‖z‖ ≥ 1}`.
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, Metric.ball c ε ⊆ f '' Metric.ball 0 1 :=
    Metric.isOpen_iff.mp (hopen _ Metric.isOpen_ball) c
      ⟨0, Metric.mem_ball_self one_pos, rfl⟩
  have hfar : ∀ z : ℂ, 1 ≤ ‖z‖ → ε ≤ ‖f z - c‖ := by
    intro z hz
    by_contra hlt
    have hlt' : ‖f z - c‖ < ε := not_le.mp hlt
    obtain ⟨w, hw, hwz⟩ := hball (by rwa [Metric.mem_ball, dist_eq_norm])
    rw [hinj hwz] at hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    linarith
  have hgne : ∀ w : ℂ, ‖w‖ < 1 → w ≠ 0 → ε ≤ ‖f w⁻¹ - c‖ := by
    intro w hw1 hw0
    apply hfar
    rw [norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.mpr hw0)).mpr hw1.le
  -- The reciprocal `g` of `f(1/w) - c` is differentiable and bounded on the
  -- punctured unit ball.
  set g : ℂ → ℂ := fun w => (f w⁻¹ - c)⁻¹ with hg_def
  have hgval : ∀ w : ℂ, ‖w‖ < 1 → w ≠ 0 → f w⁻¹ - c ≠ 0 := by
    intro w hw1 hw0 h0
    have := hgne w hw1 hw0
    rw [h0, norm_zero] at this
    linarith
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 1 \ {0}) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := by
      have := hw.1; rwa [Metric.mem_ball, dist_zero_right] at this
    have hw0 : w ≠ 0 := hw.2
    have h1 : DifferentiableAt ℂ (fun w : ℂ => f w⁻¹ - c) w :=
      ((hf w⁻¹).comp w (differentiableAt_inv hw0)).sub_const c
    exact (h1.inv (hgval w hw1 hw0)).differentiableWithinAt
  have hg_bdd : BddAbove ((norm ∘ g) '' (Metric.ball (0 : ℂ) 1 \ {0})) := by
    refine ⟨ε⁻¹, ?_⟩
    rintro x ⟨w, ⟨hw1, hw0⟩, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hw1
    have hw0' : w ≠ 0 := hw0
    simp only [Function.comp_apply, hg_def, norm_inv]
    exact inv_anti₀ hε (hgne w hw1 hw0')
  -- Removable singularity: extend `g` holomorphically across `0`.
  set G : ℂ → ℂ := Function.update g 0 (Filter.limUnder (𝓝[≠] (0 : ℂ)) g) with hG_def
  have hG_diff : DifferentiableOn ℂ G (Metric.ball 0 1) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove
      (Metric.ball_mem_nhds 0 one_pos) hg_diff hg_bdd
  have hG_an : AnalyticAt ℂ G 0 := hG_diff.analyticAt (Metric.ball_mem_nhds 0 one_pos)
  have hGg : ∀ w : ℂ, w ≠ 0 → G w = g w := fun w hw => Function.update_of_ne hw _ _
  -- `G` does not vanish identically near `0`, so it has finite analytic order `m`.
  have hG_ne_top : analyticOrderAt G 0 ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro hev
    have hev' : ∀ᶠ w in 𝓝[≠] (0 : ℂ), G w = 0 := hev.filter_mono nhdsWithin_le_nhds
    have hball1 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∈ Metric.ball (0 : ℂ) 1 :=
      Filter.eventually_mem_set.mpr (nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 one_pos))
    have hne0 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ≠ 0 :=
      Filter.eventually_mem_set.mpr self_mem_nhdsWithin
    obtain ⟨w, hGw, hw1, hw0⟩ := (hev'.and (hball1.and hne0)).exists
    rw [Metric.mem_ball, dist_zero_right] at hw1
    rw [hGg w hw0, hg_def] at hGw
    exact inv_ne_zero (hgval w hw1 hw0) hGw
  obtain ⟨m, hm⟩ : ∃ m : ℕ, analyticOrderAt G 0 = (m : ℕ∞) := by
    lift analyticOrderAt G 0 to ℕ using hG_ne_top with m hm
    exact ⟨m, rfl⟩
  obtain ⟨u, hu_an, hu0, hdecomp⟩ := (hG_an.analyticOrderAt_eq_natCast).mp hm
  have hu0norm : (0 : ℝ) < ‖u 0‖ := norm_pos_iff.mpr hu0
  have hu_lower : ∀ᶠ w in 𝓝 (0 : ℂ), ‖u 0‖ / 2 < ‖u w‖ :=
    hu_an.continuousAt.norm.eventually (eventually_gt_nhds (half_lt_self hu0norm))
  obtain ⟨δ, hδ, hδp⟩ := Metric.eventually_nhds_iff.mp (hdecomp.and hu_lower)
  -- Growth bound: `‖f z‖ ≤ C‖z‖^m` for `‖z‖ ≥ R₀`.
  set r : ℝ := min δ 1 with hr_def
  have hr : 0 < r := lt_min hδ one_pos
  have hr1 : r ≤ 1 := min_le_right δ 1
  set C : ℝ := 2 / ‖u 0‖ + ‖c‖ with hC_def
  have hC : 0 < C := by positivity
  set R₀ : ℝ := 2 / r with hR₀_def
  have hR₀1 : 1 ≤ R₀ := by
    rw [hR₀_def, le_div_iff₀ hr]
    linarith
  have hgrow : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ m := by
    intro z hz
    have hz1 : 1 ≤ ‖z‖ := le_trans hR₀1 hz
    have hz_pos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le one_pos hz1
    have hz0 : z ≠ 0 := norm_pos_iff.mp hz_pos
    set w : ℂ := z⁻¹ with hw_def
    have hw0 : w ≠ 0 := inv_ne_zero hz0
    have hwz : w⁻¹ = z := inv_inv z
    have hwnorm : ‖w‖ = ‖z‖⁻¹ := norm_inv z
    have hwr : ‖w‖ < r := by
      have h1 : r⁻¹ < ‖z‖ := by
        have h2 : r⁻¹ < R₀ := by
          rw [hR₀_def, inv_eq_one_div]
          gcongr
          norm_num
        exact lt_of_lt_of_le h2 hz
      rw [hwnorm]
      exact (inv_lt_comm₀ hz_pos hr).mpr h1
    have hw1 : ‖w‖ < 1 := lt_of_lt_of_le hwr hr1
    obtain ⟨hGw, huw⟩ := hδp (by rw [dist_zero_right]; exact lt_of_lt_of_le hwr (min_le_left δ 1))
    rw [sub_zero, smul_eq_mul, hGg w hw0] at hGw
    -- `(f z - c)⁻¹ = w^m u(w)`, hence `‖f z - c‖ ≤ (2/‖u 0‖)‖z‖^m`.
    have hval : (f z - c)⁻¹ = w ^ m * u w := by
      rw [← hwz, ← hGw, hg_def]
    have hkey : f z - c = (w ^ m * u w)⁻¹ := by rw [← hval, inv_inv]
    have h1 : ‖f z - c‖ = ‖z‖ ^ m * ‖u w‖⁻¹ := by
      rw [hkey, norm_inv, norm_mul, norm_pow, mul_inv, hwnorm, inv_pow, inv_inv]
    have h2 : ‖u w‖⁻¹ ≤ 2 / ‖u 0‖ := by
      rw [← inv_div ‖u 0‖ 2]
      exact inv_anti₀ (by positivity) huw.le
    have hub : ‖f z - c‖ ≤ ‖z‖ ^ m * (2 / ‖u 0‖) := by
      rw [h1]
      exact mul_le_mul_of_nonneg_left h2 (pow_nonneg (norm_nonneg z) m)
    have hpow1 : 1 ≤ ‖z‖ ^ m := one_le_pow₀ hz1
    have hsplit : f z = (f z - c) + c := by ring
    calc ‖f z‖ = ‖(f z - c) + c‖ := by rw [← hsplit]
      _ ≤ ‖f z - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ‖z‖ ^ m * (2 / ‖u 0‖) + ‖c‖ := by linarith
      _ ≤ ‖z‖ ^ m * (2 / ‖u 0‖) + ‖z‖ ^ m * ‖c‖ := by
          nlinarith [norm_nonneg c]
      _ = C * ‖z‖ ^ m := by rw [hC_def]; ring
  -- Cauchy estimates: all Taylor coefficients above `m` vanish.
  have hvanish : ∀ n : ℕ, m < n → iteratedDeriv n f 0 = 0 := by
    intro n hn
    have key : ∀ R : ℝ, R₀ ≤ R →
        ‖iteratedDeriv n f 0‖ ≤ (n.factorial : ℝ) * (C * R ^ m) / R ^ n := by
      intro R hR
      have hRpos : 0 < R := lt_of_lt_of_le (by linarith) hR
      apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hRpos hf.diffContOnCl
      intro z hz
      rw [mem_sphere_iff_norm, sub_zero] at hz
      calc ‖f z‖ ≤ C * ‖z‖ ^ m := hgrow z (by rw [hz]; exact hR)
        _ = C * R ^ m := by rw [hz]
    have htend : Filter.Tendsto (fun R : ℝ => (n.factorial : ℝ) * (C * R ^ m) / R ^ n)
        Filter.atTop (𝓝 0) := by
      have h0 : Filter.Tendsto (fun R : ℝ => ((n.factorial : ℝ) * C) * (R ^ m / R ^ n))
          Filter.atTop (𝓝 (((n.factorial : ℝ) * C) * 0)) :=
        (tendsto_pow_div_pow_atTop_zero hn).const_mul _
      rw [mul_zero] at h0
      exact h0.congr fun R => by ring
    have hle : ‖iteratedDeriv n f 0‖ ≤ 0 :=
      ge_of_tendsto htend (Filter.eventually_atTop.mpr ⟨R₀, key⟩)
    exact norm_le_zero_iff.mp hle
  -- Hence `f` is a polynomial of degree at most `m`.
  set p : Polynomial ℂ := ∑ n ∈ Finset.range (m + 1),
    Polynomial.C ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0) * Polynomial.X ^ n with hp_def
  have hfp : ∀ z : ℂ, f z = p.eval z := by
    intro z
    have htay : ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n = f z := by
      simpa using Complex.taylorSeries_eq_of_entire' 0 z hf
    have hsum : ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n
        = ∑ n ∈ Finset.range (m + 1), (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n := by
      refine tsum_eq_sum fun n hn => ?_
      rw [Finset.mem_range, not_lt] at hn
      rw [hvanish n hn]
      ring
    rw [← htay, hsum, hp_def, Polynomial.eval_finsetSum]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  -- Injectivity forces degree one, via the fiber of `f` over `c = f 0`:
  -- `p - C c` splits with all roots equal to `0`, so `f z = a z^N + c`.
  set N : ℕ := p.natDegree with hN_def
  have hN0 : N ≠ 0 := by
    intro h
    apply hne
    have hpc := Polynomial.eq_C_of_natDegree_eq_zero (hN_def ▸ h)
    rw [hc_def, hfp 0, hfp 1, hpc]
    simp
  set q : Polynomial ℂ := p - Polynomial.C c with hq_def
  have hqdeg : q.natDegree = N := Polynomial.natDegree_sub_C
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hqdeg
    exact hN0 hqdeg.symm
  have hcard : q.roots.card = q.natDegree :=
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits q)
  have hroots : ∀ x ∈ q.roots, x = 0 := by
    intro x hx
    have hrx := Polynomial.isRoot_of_mem_roots hx
    rw [Polynomial.IsRoot, hq_def, Polynomial.eval_sub, Polynomial.eval_C] at hrx
    apply hinj
    rw [hfp x, ← hc_def]
    linear_combination hrx
  have hrepl : q.roots = Multiset.replicate N 0 :=
    Multiset.eq_replicate.mpr ⟨hcard.trans hqdeg, hroots⟩
  have hfact := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [hrepl, Multiset.map_replicate, Multiset.prod_replicate, Polynomial.C_0,
    sub_zero] at hfact
  set a : ℂ := q.leadingCoeff with ha_def
  have ha0 : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
  have hfz : ∀ z : ℂ, f z = a * z ^ N + c := by
    intro z
    have hev := congrArg (Polynomial.eval z) hfact
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      hq_def, Polynomial.eval_sub] at hev
    rw [hfp z]
    linear_combination -hev
  -- Degree at least two would contradict injectivity via a root of unity.
  have hN1 : N = 1 := by
    by_contra hN1
    have hprim := Complex.isPrimitiveRoot_exp N hN0
    have hζ : f (Complex.exp (2 * Real.pi * Complex.I / N)) = f 1 := by
      rw [hfz, hfz, hprim.pow_eq_one, one_pow]
    exact hprim.ne_one (by omega) (hinj hζ)
  refine ⟨a, c, ha0, funext fun z => ?_⟩
  rw [hfz z, hN1, pow_one]

/-- **The transition map of two solutions of the same Beltrami equation is
conformal.** If `f₁, f₂` are quasiconformal solutions for the same coefficient `b`,
the composition `f₂ ∘ f₁⁻¹` is entire: at almost every point the chain rule composes
the differential of `f₂` with the inverse differential of `f₁`, and equal Beltrami
ratios make the product complex-linear; the composition is quasiconformal (through
the geometric track), so a vanishing-coefficient witness applies Weyl's lemma. -/
theorem differentiable_comp_inverse_of_isQCAnalytic {b : BeltramiCoeff}
    {f₁ f₂ : ℂ → ℂ} (h₁ : IsQCAnalytic f₁ b) (h₂ : IsQCAnalytic f₂ b) :
    Differentiable ℂ (f₂ ∘ ⇑(h₁.1.1.homeomorph f₁).symm) := by
  classical
  set g : ℂ → ℂ := ⇑(h₁.1.1.homeomorph f₁).symm with hg
  -- Inversion identities for `g = f₁⁻¹`.
  have hfwd : ∀ z, (h₁.1.1.homeomorph f₁) z = f₁ z := fun z =>
    IsHomeomorph.homeomorph_apply f₁ h₁.1.1 z
  have hfg : ∀ w, f₁ (g w) = w := fun w => by
    rw [hg, ← hfwd ((h₁.1.1.homeomorph f₁).symm w)]
    exact (h₁.1.1.homeomorph f₁).apply_symm_apply w
  have hgcont : Continuous g := (h₁.1.1.homeomorph f₁).continuous_symm
  -- ===== (A)+(B): `f₂ ∘ g` is quasiconformal, through the geometric track. =====
  have hm0 := b.normInf_nonneg
  have hm1 := b.normInf_lt_one
  have hK1 : 1 ≤ b.K := b.one_le_K
  have hbnd : b.normInf ≤ (b.K - 1) / (b.K + 1) := by
    have hden : (0 : ℝ) < 1 - b.normInf := by linarith
    have hKval : b.K = (1 + b.normInf) / (1 - b.normInf) := rfl
    have hKeq : b.K * (1 - b.normInf) = 1 + b.normInf := by
      rw [hKval, div_mul_cancel₀ _ (ne_of_gt hden)]
    have hKpos : (0 : ℝ) < b.K + 1 := by linarith
    rw [le_div_iff₀ hKpos]
    nlinarith [hKeq]
  have h₁geom : IsQCGeometric f₁ b.K := isQCGeometric_of_isQCAnalytic hK1 hbnd h₁
  have h₂geom : IsQCGeometric f₂ b.K := isQCGeometric_of_isQCAnalytic hK1 hbnd h₂
  -- The two homeomorph-derived inverses of `f₁` agree, so `g` is geometric `K`-qc.
  have hbridge : ⇑(h₁geom.2.1.isHomeomorph.homeomorph f₁).symm = g := by
    funext w
    have hinj : Function.Injective f₁ := (h₁.1.1.homeomorph f₁).injective
    have hL : f₁ ((h₁geom.2.1.isHomeomorph.homeomorph f₁).symm w) = w := by
      rw [← IsHomeomorph.homeomorph_apply f₁ h₁geom.2.1.isHomeomorph
            ((h₁geom.2.1.isHomeomorph.homeomorph f₁).symm w)]
      exact (h₁geom.2.1.isHomeomorph.homeomorph f₁).apply_symm_apply w
    exact hinj (hL.trans (hfg w).symm)
  have hg_geom : IsQCGeometric g b.K :=
    hbridge ▸ isQCGeometric_inv_of_isQCGeometric h₁geom
  have hφgeom : IsQCGeometric (f₂ ∘ g) (b.K * b.K) := h₂geom.comp hg_geom
  obtain ⟨b', hb', hφana⟩ :=
    isQCAnalytic_of_isQCGeometric (by nlinarith [hK1, sq_nonneg (b.K - 1)]) hφgeom
  -- ===== (C): `∂̄(f₂ ∘ g) = 0` almost everywhere, by the a.e. chain rule. =====
  -- The a.e. good set on the `z`-side.
  have hzpack : ∀ᵐ z, DifferentiableAt ℝ f₁ z ∧ 0 < (fderiv ℝ f₁ z).det ∧
      dzbar f₁ z = b.μ z * dz f₁ z ∧ DifferentiableAt ℝ f₂ z ∧
      dzbar f₂ z = b.μ z * dz f₂ z := by
    filter_upwards [IsQCAnalytic.ae_differentiableAt h₁, h₁.1.2, h₁.2.2,
      IsQCAnalytic.ae_differentiableAt h₂, h₂.2.2] with z hz1 hz2 hz3 hz4 hz5
    exact ⟨hz1, hz2, hz3, hz4, hz5⟩
  -- Forward Lusin (N) for `f₁`: null sets have null images.
  have hLusin : ∀ S : Set ℂ, volume S = 0 → volume (f₁ '' S) = 0 := by
    obtain ⟨p, gx, gy, hp2, hgrad, hgxp, hgyp⟩ := h₁.exists_weakGradient_memLpLocOn_gt_two
    exact fun S hS =>
      lusinN_image_null_of_weakGradient hp2 h₁.1.1.continuous hgrad hgxp hgyp hS
  -- Transfer to the `w`-side: the bad `w`-set lies in `f₁ '' (bad z-set)`, hence is null.
  have hwgood : ∀ᵐ w, DifferentiableAt ℝ f₁ (g w) ∧ 0 < (fderiv ℝ f₁ (g w)).det ∧
      dzbar f₁ (g w) = b.μ (g w) * dz f₁ (g w) ∧ DifferentiableAt ℝ f₂ (g w) ∧
      dzbar f₂ (g w) = b.μ (g w) * dz f₂ (g w) := by
    refine ae_iff.mpr (measure_mono_null ?_ (hLusin _ (ae_iff.mp hzpack)))
    intro w hw
    exact ⟨g w, hw, hfg w⟩
  -- Pointwise representation of the real differential by Wirtinger derivatives:
  -- `Df(v) = ∂f · v + ∂̄f · conj v`.
  have hrepr : ∀ (F : ℂ → ℂ) (ζ v : ℂ),
      (fderiv ℝ F ζ) v = dz F ζ * v + dzbar F ζ * (starRingEnd ℂ) v := by
    intro F ζ v
    set T : ℂ →L[ℝ] ℂ := fderiv ℝ F ζ with hT
    have hTv : T v = (v.re : ℂ) * T 1 + (v.im : ℂ) * T Complex.I := by
      conv_lhs => rw [show v = v.re • (1 : ℂ) + v.im • Complex.I by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hcv : (starRingEnd ℂ) v = (v.re : ℂ) - (v.im : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im v]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hv : v = (v.re : ℂ) + (v.im : ℂ) * Complex.I := (Complex.re_add_im v).symm
    simp only [dz, dzbar, ← hT]
    rw [hTv, hcv]
    linear_combination (-(1 / 2 : ℂ) * (T 1 - Complex.I * T Complex.I)) * hv +
      ((v.im : ℂ) * T Complex.I) * Complex.I_sq
  -- The pointwise chain-rule computation.
  have hCzero : ∀ᵐ w, dzbar (f₂ ∘ g) w = 0 := by
    filter_upwards [hwgood] with w hw
    obtain ⟨hdiff₁, hdet₁, hbel₁, hdiff₂, hbel₂⟩ := hw
    -- The inverse differential of `f₁` at `g w` (easy half of the IFT).
    have hdetne : (fderiv ℝ f₁ (g w)).det ≠ 0 := ne_of_gt hdet₁
    set e : ℂ ≃L[ℝ] ℂ := (fderiv ℝ f₁ (g w)).toContinuousLinearEquivOfDetNeZero hdetne
      with he
    have hecoe : (e : ℂ →L[ℝ] ℂ) = fderiv ℝ f₁ (g w) :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hdetne
    have hfd₁ : HasFDerivAt f₁ (e : ℂ →L[ℝ] ℂ) (g w) := by
      rw [hecoe]; exact hdiff₁.hasFDerivAt
    have hloc : ∀ᶠ y in nhds w, f₁ (g y) = y := Filter.Eventually.of_forall hfg
    have hgfd : HasFDerivAt g (e.symm : ℂ →L[ℝ] ℂ) w :=
      HasFDerivAt.of_local_left_inverse hgcont.continuousAt hfd₁ hloc
    have hφfd : HasFDerivAt (f₂ ∘ g)
        ((fderiv ℝ f₂ (g w)).comp (e.symm : ℂ →L[ℝ] ℂ)) w :=
      (hdiff₂.hasFDerivAt).comp w hgfd
    have hfφ : fderiv ℝ (f₂ ∘ g) w = (fderiv ℝ f₂ (g w)).comp (e.symm : ℂ →L[ℝ] ℂ) :=
      hφfd.fderiv
    -- `∂f₁ ≠ 0` at `g w`, from the positive Jacobian.
    have hpBne : dz f₁ (g w) ≠ 0 := by
      intro h0
      have hdd := det_fderiv_eq_wirtinger f₁ (g w)
      rw [h0, norm_zero] at hdd
      nlinarith [hdet₁, sq_nonneg ‖dzbar f₁ (g w)‖]
    -- The defining equations of the inverse differential at the basis directions.
    have hBs : ∀ u : ℂ, (fderiv ℝ f₁ (g w)) (e.symm u) = u := by
      intro u
      rw [← hecoe]
      simp
    have h1 : dz f₁ (g w) * e.symm 1
        + dzbar f₁ (g w) * (starRingEnd ℂ) (e.symm 1) = 1 := by
      rw [← hrepr f₁ (g w) (e.symm 1)]; exact hBs 1
    have hI : dz f₁ (g w) * e.symm Complex.I
        + dzbar f₁ (g w) * (starRingEnd ℂ) (e.symm Complex.I) = Complex.I := by
      rw [← hrepr f₁ (g w) (e.symm Complex.I)]; exact hBs Complex.I
    -- Beltrami cancellation: the `∂̄`-combination of the inverse differential vanishes.
    have hbr : e.symm 1 + b.μ (g w) * (starRingEnd ℂ) (e.symm 1)
        + Complex.I * (e.symm Complex.I
          + b.μ (g w) * (starRingEnd ℂ) (e.symm Complex.I)) = 0 := by
      have hkey : dz f₁ (g w) * (e.symm 1 + b.μ (g w) * (starRingEnd ℂ) (e.symm 1)
          + Complex.I * (e.symm Complex.I
            + b.μ (g w) * (starRingEnd ℂ) (e.symm Complex.I))) = 0 := by
        linear_combination h1 + Complex.I * hI + Complex.I_sq
          - ((starRingEnd ℂ) (e.symm 1)
              + Complex.I * (starRingEnd ℂ) (e.symm Complex.I)) * hbel₁
      exact (mul_eq_zero.mp hkey).resolve_left hpBne
    -- Assemble `∂̄(f₂ ∘ g) w = 0`.
    simp only [dzbar, hfφ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [hrepr f₂ (g w) (e.symm 1), hrepr f₂ (g w) (e.symm Complex.I)]
    linear_combination (dz f₂ (g w) / 2) * hbr +
      (((starRingEnd ℂ) (e.symm 1) + Complex.I * (starRingEnd ℂ) (e.symm Complex.I)) / 2)
        * hbel₂
  -- ===== Weyl's lemma with the zero coefficient. =====
  have hb₀bound : eLpNormEssSup (fun _ : ℂ => (0 : ℂ)) volume < 1 := by
    rw [show (fun _ : ℂ => (0 : ℂ)) = (0 : ℂ → ℂ) from rfl, eLpNormEssSup_zero]
    exact zero_lt_one
  refine weyl_lemma (b := ⟨fun _ => 0, measurable_const, hb₀bound⟩)
    ⟨hφana.1, hφana.2.1, ?_⟩ rfl
  filter_upwards [hCzero] with w hwz
  rw [hwz]
  simp

/-- **The measurable Riemann mapping theorem, uniqueness half.** There is exactly
one quasiconformal solution of the Beltrami equation fixing `0` and `1`
(the plane normalization; infinity is fixed by every homeomorphism of `ℂ`). -/
theorem mrmt_unique_normalized (b : BeltramiCoeff) :
    ∃! f : ℂ → ℂ, IsQCAnalytic f b ∧ f 0 = 0 ∧ f 1 = 1 := by
  classical
  -- ===== Existence: normalize a solution from the existence half. =====
  obtain ⟨f₀, hf₀⟩ := mrmt_exists b
  have hf₀cont : Continuous f₀ := hf₀.1.1.continuous
  have hne : f₀ 1 - f₀ 0 ≠ 0 :=
    sub_ne_zero.mpr fun h => one_ne_zero ((hf₀.1.1.homeomorph f₀).injective h)
  set a : ℂ := (f₀ 1 - f₀ 0)⁻¹ with hadef
  have ha0 : a ≠ 0 := inv_ne_zero hne
  set f : ℂ → ℂ := fun z => a * (f₀ z - f₀ 0) with hfdef
  have hfz : ∀ z, f z = a * (f₀ z - f₀ 0) := fun _ => rfl
  have hf0 : f 0 = 0 := by rw [hfz, sub_self, mul_zero]
  have hf1 : f 1 = 1 := by rw [hfz]; exact inv_mul_cancel₀ hne
  have hfcont : Continuous f := continuous_const.mul (hf₀cont.sub continuous_const)
  -- `f` is a homeomorphism: an affine conformal map post-composed with `f₀`.
  have hhomeo : IsHomeomorph f := by
    have hcomp : IsHomeomorph (affineMap a (-(a * f₀ 0)) ∘ f₀) :=
      (affineMap_isHomeomorph ha0 _).comp hf₀.1.1
    have heq : affineMap a (-(a * f₀ 0)) ∘ f₀ = f := by
      funext z
      change a * f₀ z + -(a * f₀ 0) = a * (f₀ z - f₀ 0)
      ring
    rwa [heq] at hcomp
  -- Jacobian positivity and the Beltrami equation, by Wirtinger scaling.
  have hae : ∀ᵐ z, 0 < (fderiv ℝ f z).det ∧ dzbar f z = b.μ z * dz f z := by
    filter_upwards [IsQCAnalytic.ae_differentiableAt hf₀, hf₀.1.2, hf₀.2.2]
      with z hz1 hz2 hz3
    have hfd : HasFDerivAt f (a • fderiv ℝ f₀ z) z :=
      (hz1.hasFDerivAt.sub_const (f₀ 0)).const_mul a
    have hffderiv : fderiv ℝ f z = a • fderiv ℝ f₀ z := hfd.fderiv
    have hdzf : dz f z = a * dz f₀ z := by
      simp only [dz, hffderiv, smul_apply, smul_eq_mul]
      ring
    have hdzbarf : dzbar f z = a * dzbar f₀ z := by
      simp only [dzbar, hffderiv, smul_apply, smul_eq_mul]
      ring
    refine ⟨?_, ?_⟩
    · have key : (fderiv ℝ f z).det = ‖a‖ ^ 2 * (fderiv ℝ f₀ z).det := by
        rw [det_fderiv_eq_wirtinger f z, det_fderiv_eq_wirtinger f₀ z, hdzf, hdzbarf,
          norm_mul, norm_mul]
        ring
      rw [key]
      exact mul_pos (pow_pos (norm_pos_iff.mpr ha0) 2) hz2
    · rw [hdzbarf, hz3, hdzf]
      ring
  -- `W^{1,2}_loc` membership: scale the weak gradient of `f₀`.
  obtain ⟨hf₀L2, gx, gy, ⟨hwgx, hwgy⟩, hmgx, hmgy⟩ := hf₀.2.1
  have hLpgx : MemLpLocOn gx 2 Set.univ := hmgx
  have hLpgy : MemLpLocOn gy 2 Set.univ := hmgy
  have memLpLoc_to_li : ∀ {h : ℂ → ℂ}, MemLpLocOn h 2 Set.univ →
      MeasureTheory.LocallyIntegrable h := by
    intro h hh
    rw [← locallyIntegrableOn_univ, locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    have : MeasureTheory.IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    have hmem1 : MemLp h 1 (volume.restrict k) :=
      (hh k (Set.subset_univ _) hk).mono_exponent (by norm_num)
    exact memLp_one_iff_integrable.mp hmem1
  have hf₀LIon : LocallyIntegrableOn f₀ Set.univ :=
    locallyIntegrableOn_univ.mpr hf₀cont.locallyIntegrable
  have hcLIon : LocallyIntegrableOn (fun _ : ℂ => f₀ 0) Set.univ :=
    locallyIntegrableOn_univ.mpr continuous_const.locallyIntegrable
  have h0LIon : LocallyIntegrableOn (fun _ : ℂ => (0 : ℂ)) Set.univ :=
    locallyIntegrableOn_univ.mpr continuous_const.locallyIntegrable
  have hgxLIon : LocallyIntegrableOn gx Set.univ :=
    locallyIntegrableOn_univ.mpr (memLpLoc_to_li hLpgx)
  have hgyLIon : LocallyIntegrableOn gy Set.univ :=
    locallyIntegrableOn_univ.mpr (memLpLoc_to_li hLpgy)
  -- Weak-derivative transfer: `∂ᵥ(a·(f₀ − f₀ 0)) = a·∂ᵥf₀` weakly.
  have hkey : ∀ {vd : ℂ} {gv : ℂ → ℂ}, HasWeakDirDeriv vd gv f₀ Set.univ →
      LocallyIntegrableOn gv Set.univ →
      HasWeakDirDeriv vd (fun z => a * gv z) f Set.univ := by
    intro vd gv hgv hgvli
    have hconst : HasWeakDirDeriv vd
        (fun z : ℂ => (fderiv ℝ (fun _ : ℂ => f₀ 0) z) vd) (fun _ : ℂ => f₀ 0)
        Set.univ :=
      HasWeakDirDeriv.of_contDiffOn isOpen_univ contDiffOn_const
    have heq0 : (fun z : ℂ => (fderiv ℝ (fun _ : ℂ => f₀ 0) z) vd)
        = fun _ : ℂ => (0 : ℂ) := by
      funext z
      simp
    rw [heq0] at hconst
    have hsmul := (hgv.sub hconst hf₀LIon hcLIon hgvli h0LIon).const_smul a
    have heq1 : (fun z => a • (gv z - (0 : ℂ))) = fun z => a * gv z := by
      funext z
      rw [smul_eq_mul, sub_zero]
    have heq2 : (fun z => a • (f₀ z - f₀ 0)) = f := funext fun _ => rfl
    rwa [heq1, heq2] at hsmul
  have hfL2 : MemLpLocOn f 2 Set.univ := by
    intro Kc _ hKc
    have : MeasureTheory.IsFiniteMeasure (volume.restrict Kc) :=
      ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hfcont.continuousOn
    have hmeas : AEStronglyMeasurable f (volume.restrict Kc) :=
      hfcont.aestronglyMeasurable
    have hbound : ∀ᵐ x ∂(volume.restrict Kc), ‖f x‖ ≤ C := by
      rw [ae_restrict_iff' hKc.measurableSet]
      exact Filter.Eventually.of_forall hC
    exact (memLp_top_of_bound hmeas C hbound).mono_exponent le_top
  have hgxL2' : MemLpLocOn (fun z => a * gx z) 2 Set.univ := fun K hK1 hK2 =>
    (hLpgx K hK1 hK2).const_mul a
  have hgyL2' : MemLpLocOn (fun z => a * gy z) 2 Set.univ := fun K hK1 hK2 =>
    (hLpgy K hK1 hK2).const_mul a
  have hfW12 : MemW12loc f :=
    ⟨hfL2, fun z => a * gx z, fun z => a * gy z,
      ⟨hkey hwgx hgxLIon, hkey hwgy hgyLIon⟩, hgxL2', hgyL2'⟩
  have hfa : IsQCAnalytic f b :=
    ⟨⟨hhomeo, hae.mono fun z hz => hz.1⟩, hfW12, hae.mono fun z hz => hz.2⟩
  -- ===== Package existence; uniqueness via the affine transition map. =====
  refine ⟨f, ⟨hfa, hf0, hf1⟩, ?_⟩
  rintro f' ⟨hf'a, hf'0, hf'1⟩
  -- The transition map `φ = f' ∘ f⁻¹` is entire and injective, hence affine.
  have hφdiff : Differentiable ℂ (f' ∘ ⇑(hfa.1.1.homeomorph f).symm) :=
    differentiable_comp_inverse_of_isQCAnalytic hfa hf'a
  have hφinj : Function.Injective (f' ∘ ⇑(hfa.1.1.homeomorph f).symm) :=
    ((hf'a.1.1.homeomorph f').injective).comp (hfa.1.1.homeomorph f).symm.injective
  obtain ⟨A, C, hA0, hφeq⟩ := eq_affine_of_differentiable_of_injective hφdiff hφinj
  -- The two-point normalization pins `A = 1`, `C = 0`.
  have hg0 : (hfa.1.1.homeomorph f).symm 0 = 0 := by
    rw [Homeomorph.symm_apply_eq, IsHomeomorph.homeomorph_apply f hfa.1.1, hf0]
  have hg1 : (hfa.1.1.homeomorph f).symm 1 = 1 := by
    rw [Homeomorph.symm_apply_eq, IsHomeomorph.homeomorph_apply f hfa.1.1, hf1]
  have hC : C = 0 := by
    have h0 := congrFun hφeq 0
    simp only [Function.comp_apply, hg0, hf'0, mul_zero, zero_add] at h0
    exact h0.symm
  have hA : A = 1 := by
    have h1 := congrFun hφeq 1
    simp only [Function.comp_apply, hg1, hf'1, mul_one, hC, add_zero] at h1
    exact h1.symm
  -- `φ = id` transfers back to `f' = f`.
  funext z
  have hsymmf : (hfa.1.1.homeomorph f).symm (f z) = z := by
    rw [← IsHomeomorph.homeomorph_apply f hfa.1.1 z]
    exact (hfa.1.1.homeomorph f).symm_apply_apply z
  have hz := congrFun hφeq (f z)
  simp only [Function.comp_apply, hsymmf] at hz
  rw [hz, hA, hC, one_mul, add_zero]

end NoWanderingDomains
