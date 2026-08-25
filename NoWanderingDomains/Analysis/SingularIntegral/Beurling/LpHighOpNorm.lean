/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.Beurling.LpLow

/-!
# The Beurling transform — LpHighOpNorm

`Lᵖ` boundedness for `p > 2` by kernel-symmetry duality, the full Calderón–Zygmund
bound `beurling_lp_bound` (all `1 < p < ∞`), and the Riesz–Thorin operator-norm
continuity `beurling_opNorm_continuous`.

Part of the `Beurling` development (overview in `Beurling/Kernel.lean`). -/

open MeasureTheory Complex Filter Topology
open scoped Real ENNReal NNReal Convolution InnerProductSpace

namespace NoWanderingDomains

variable {μ : ℂ → ℂ} {z : ℂ} {p : ℝ≥0∞}

/-! ## `Lᵖ` boundedness for `p > 2` by duality

The Beurling kernel is symmetric (`beurlingKernel_symm`), so the truncated
operator is its own transpose w.r.t. the bilinear pairing `∫ f·g`. For
`BoundedFiniteSupport` `f` (hence `f ∈ L¹`) the double integral is absolutely
convergent, so Fubini gives the truncation symmetry against any `g ∈ Lᵖ'`. By
duality (`eLpNorm_le_iSup_integral_mul`) and the `Lᵖ'` truncation bound (`p' < 2`,
`eLpNorm_czOperator_beurling_Lp`), `‖czOp r f‖_p ≤ C_{p'} ‖f‖_p`. The maximal
operator + a.e.-convergence development then transfers (as for `p < 2`) to
`beurling`. -/

/-- **Truncation symmetry.** For `f` of bounded finite support (hence in `L¹`) and
`g ∈ Lᵖ'`, the symmetric Beurling kernel and Fubini give
`∫ (czOp r f)·g = ∫ f·(czOp r g)`. -/
lemma czOperator_beurling_pairing_symm {p p' : ℝ≥0∞} (hp1 : 1 < p) (hp_top : p ≠ ⊤)
    [ENNReal.HolderConjugate p p'] {r : ℝ} (hr : 0 < r) {f g : ℂ → ℂ}
    (hf : BoundedFiniteSupport f volume) (hg : MemLp g p' volume) :
    ∫ x, czOperator beurlingKernel r f x * g x ∂volume
      = ∫ x, f x * czOperator beurlingKernel r g x ∂volume := by
  have : ENNReal.HolderConjugate p' p := ENNReal.HolderConjugate.symm
  have hp'_top : p' ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr hp1).ne
  have hp'1 : 1 < p' :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp (lt_of_le_of_ne le_top hp_top)
  have hf' : MemLp f p volume := hf.memLp p
  have hfint : Integrable f volume := hf.integrable
  -- For every `y`, the symmetric set `{x | r ≤ dist x y}` equals `(ball y r)ᶜ`.
  have hsetEq : ∀ y : ℂ, {x : ℂ | r ≤ dist x y} = (Metric.ball y r)ᶜ := by
    intro y; ext x; simp [Metric.mem_ball, not_lt, dist_comm]
  -- The kernel section centered at `y`, at exponent `p`, is in `Lᵖ`
  -- (`∫_{|u|≥r} |u|^{-2 p.toReal} < ∞` since `p.toReal > 1`), with a `y`-independent
  -- `Lᵖ` lintegral `Kr_lint = ∫⁻_{|u|≥r} ((‖u‖²)⁻¹)^{p.toReal}`.
  set q : ℝ := p.toReal with hq_def
  have hp0 : p ≠ 0 := by rintro rfl; exact absurd hp1 (by simp)
  have hq1 : 1 < q := by
    rw [hq_def, show (1:ℝ) = (1 : ℝ≥0∞).toReal from rfl]
    exact ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top |>.mpr hp1
  have hq0 : 0 < q := lt_trans one_pos hq1
  -- `y`-independent finiteness of the kernel-section `Lᵖ` lintegral.
  have hlint : ∫⁻ u : ℂ in {u : ℂ | r ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q < ⊤ := by
    rw [← lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
      ← Complex.lintegral_comp_polarCoord_symm]
    set box : ℝ × ℝ → ENNReal := fun p =>
      (Set.Ici r ×ˢ Set.Ioo (-π) π).indicator
        (fun p => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q)) p with hbox
    have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q)) := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.mul measurable_fst
      exact (Real.continuous_rpow_const hq0.le).measurable.comp ((measurable_fst.pow_const 2).inv)
    have hbound : ∀ pp ∈ polarCoord.target,
        ENNReal.ofReal pp.1 • {u : ℂ | r ≤ ‖u‖}.indicator
          (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q) (Complex.polarCoord.symm pp) ≤ box pp := by
      intro pp hpp
      rw [polarCoord_target, Set.mem_prod] at hpp
      obtain ⟨hpp1, hpp2⟩ := hpp
      simp only [Set.mem_Ioi] at hpp1
      simp only [hbox]
      have hnorm : ‖Complex.polarCoord.symm pp‖ = pp.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hpp1]
      by_cases hmem : Complex.polarCoord.symm pp ∈ {u : ℂ | r ≤ ‖u‖}
      · have hpR : r ≤ pp.1 := by rw [Set.mem_ofPred_eq, hnorm] at hmem; exact hmem
        rw [Set.indicator_of_mem hmem,
          Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hpR, hpp2⟩)]
        have henorm : ‖Complex.polarCoord.symm pp‖ₑ = ENNReal.ofReal pp.1 := by
          rw [← ofReal_norm, hnorm]
        rw [henorm, smul_eq_mul,
          show ((ENNReal.ofReal pp.1 ^ 2)⁻¹) ^ q = ENNReal.ofReal (((pp.1^2)⁻¹)^q) by
            rw [← ENNReal.ofReal_pow hpp1.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
              ENNReal.ofReal_rpow_of_pos (by positivity)],
          ← ENNReal.ofReal_mul hpp1.le]
      · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le
    refine lt_of_le_of_lt (setLIntegral_mono
      (hmeas_polar.indicator (measurableSet_Ici.prod measurableSet_Ioo)) hbound) ?_
    calc ∫⁻ pp in polarCoord.target, box pp
        ≤ ∫⁻ pp, box pp := setLIntegral_le_lintegral _ _
      _ = ∫⁻ pp in (Set.Ici r ×ˢ Set.Ioo (-π) π), ENNReal.ofReal (pp.1 * ((pp.1^2)⁻¹)^q) := by
            rw [hbox, lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hmeas_polar.aemeasurable]
            simp only [setLIntegral_const]
            rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
            apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
            have hint : IntegrableOn (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q) (Set.Ici r) volume := by
              have heq : (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q)
                  =ᶠ[ae (volume.restrict (Set.Ici r))]
                  (fun ρ : ℝ => ρ^(1 - 2 * q)) := by
                filter_upwards [ae_restrict_mem measurableSet_Ici] with ρ hρ
                simp only [Set.mem_Ici] at hρ
                have hρpos : 0 < ρ := lt_of_lt_of_le hr hρ
                have hbase : (ρ^2)⁻¹ = ρ^(-2 : ℝ) := by
                  rw [Real.rpow_neg hρpos.le, ← Real.rpow_natCast ρ 2]; norm_num
                have h1 : ((ρ^2)⁻¹)^q = ρ^(-2 * q) := by
                  rw [hbase, ← Real.rpow_mul hρpos.le]
                have h2 : ρ * ρ^(-2 * q) = ρ^(1 - 2 * q) := by
                  nth_rewrite 1 [← Real.rpow_one ρ]
                  rw [← Real.rpow_add hρpos]; congr 1; ring
                rw [h1, h2]
              rw [integrableOn_congr_fun_ae heq, integrableOn_Ici_iff_integrableOn_Ioi,
                integrableOn_Ioi_rpow_iff hr]
              nlinarith [hq1]
            have hfin := hint.2
            rw [hasFiniteIntegral_iff_enorm] at hfin
            refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y hy => ?_)) hfin
            · refine (measurable_id.mul ?_).enorm
              exact (Real.continuous_rpow_const hq0.le).measurable.comp
                ((measurable_id.pow_const 2).inv)
            · simp only [Set.mem_Ici] at hy
              have hypos : 0 < y := lt_of_lt_of_le hr hy
              rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- The kernel section centered at `y` lies in `Lᵖ`, with a `y`-independent `Lᵖ` norm bound.
  have hkermem_p : ∀ y : ℂ,
      eLpNorm (fun x => (Metric.ball y r)ᶜ.indicator (fun x => beurlingKernel y x) x) p volume
        ≤ (∫⁻ u : ℂ in {u : ℂ | r ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q) ^ (1 / q) := by
    intro y
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top, ← hq_def, one_div]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    have hpt : ∀ x, ‖(Metric.ball y r)ᶜ.indicator (fun x => beurlingKernel y x) x‖ₑ ^ q
        = (Metric.ball y r)ᶜ.indicator (fun x => ‖beurlingKernel y x‖ₑ ^ q) x := by
      intro x
      by_cases h : x ∈ (Metric.ball y r)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero,
          ENNReal.zero_rpow_of_pos hq0]
    refine le_of_eq_of_le (lintegral_congr hpt) ?_
    rw [lintegral_indicator measurableSet_ball.compl]
    have hkb : ∀ x, ‖beurlingKernel y x‖ₑ ^ q ≤ ((‖y - x‖ₑ ^ 2)⁻¹) ^ q := by
      intro x
      apply ENNReal.rpow_le_rpow _ hq0.le
      by_cases h : y = x
      · subst h; simp [beurlingKernel]
      · have hne : y - x ≠ 0 := sub_ne_zero.mpr h
        have he : beurlingKernel y x = ((y-x) * (y-x))⁻¹ := by
          rw [beurlingKernel, zpow_neg, zpow_two]
        rw [he, enorm_inv (mul_ne_zero hne hne), enorm_mul, sq]
    refine le_trans (setLIntegral_mono ?_ (fun x _ => hkb x)) ?_
    · exact ENNReal.continuous_rpow_const.measurable.comp
        ((((measurable_const.sub measurable_id).enorm).pow_const 2).inv)
    rw [← lintegral_indicator measurableSet_ball.compl]
    have hsub : (fun x => (Metric.ball y r)ᶜ.indicator (fun x => ((‖y - x‖ₑ ^ 2)⁻¹) ^ q) x)
        = (fun x => {u : ℂ | r ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q) (y - x)) := by
      funext x
      have hiff : (x ∈ (Metric.ball y r)ᶜ) ↔ (y - x ∈ {u : ℂ | r ≤ ‖u‖}) := by
        rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_ofPred_eq, dist_comm,
          Complex.dist_eq]
      by_cases h : x ∈ (Metric.ball y r)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
    rw [hsub, lintegral_sub_left_eq_self
      (fun u => {u : ℂ | r ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q) u) y]
    rw [lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable)]
  -- The `y`-independent Hölder constant.
  set Kr : ℝ≥0∞ := (∫⁻ u : ℂ in {u : ℂ | r ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q) ^ (1 / q) with hKr_def
  have hKr_ne_top : Kr ≠ ⊤ := by
    rw [hKr_def]; finiteness
  -- The Fubini integrand, oriented with the `L¹` variable `y` first.
  set F : ℂ → ℂ → ℂ := fun y x =>
    (Metric.ball y r)ᶜ.indicator (fun x => beurlingKernel y x * f y * g x) x with hF_def
  -- Pointwise: `∫ x, F y x = f y * czOperator beurlingKernel r g y` (kernel symmetry).
  have hFy : ∀ y, ∫ x, F y x = f y * czOperator beurlingKernel r g y := by
    intro y
    change ∫ x, (Metric.ball y r)ᶜ.indicator (fun x => beurlingKernel y x * f y * g x) x
      = f y * czOperator beurlingKernel r g y
    rw [integral_indicator measurableSet_ball.compl]
    change (∫ x in (Metric.ball y r)ᶜ, beurlingKernel y x * f y * g x)
      = f y * ∫ x in (Metric.ball y r)ᶜ, beurlingKernel y x * g x
    rw [show (f y * ∫ x in (Metric.ball y r)ᶜ, beurlingKernel y x * g x)
          = ∫ x in (Metric.ball y r)ᶜ, f y * (beurlingKernel y x * g x) from
        (integral_const_mul _ _).symm]
    refine setIntegral_congr_fun measurableSet_ball.compl (fun x _ => ?_)
    show beurlingKernel y x * f y * g x = f y * (beurlingKernel y x * g x)
    ring
  -- Pointwise: `∫ y, F y x = (czOperator beurlingKernel r f x) * g x`.
  have hFx : ∀ x, ∫ y, F y x = czOperator beurlingKernel r f x * g x := by
    intro x
    have hindEq : (fun y => F y x)
        = fun y => (Metric.ball x r)ᶜ.indicator
            (fun y => g x * (beurlingKernel x y * f y)) y := by
      funext y
      change (Metric.ball y r)ᶜ.indicator (fun x => beurlingKernel y x * f y * g x) x
        = (Metric.ball x r)ᶜ.indicator (fun y => g x * (beurlingKernel x y * f y)) y
      by_cases h : x ∈ Metric.ball y r
      · have hyc : y ∉ (Metric.ball x r)ᶜ := by
          simp only [Set.mem_compl_iff, Metric.mem_ball, not_not]
          rw [Metric.mem_ball, dist_comm] at h; exact h
        have hxc : x ∉ (Metric.ball y r)ᶜ := by simp [h]
        rw [Set.indicator_of_notMem hxc, Set.indicator_of_notMem hyc]
      · have hyc : y ∈ (Metric.ball x r)ᶜ := by
          simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt]
          rw [Metric.mem_ball, dist_comm, not_lt] at h; exact h
        have hxc : x ∈ (Metric.ball y r)ᶜ := by simp [h]
        rw [Set.indicator_of_mem hxc, Set.indicator_of_mem hyc, beurlingKernel_symm y x]; ring
    rw [hindEq, integral_indicator measurableSet_ball.compl]
    rw [show (∫ y in (Metric.ball x r)ᶜ, g x * (beurlingKernel x y * f y))
          = g x * ∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * f y from
        integral_const_mul _ _]
    change g x * czOperator beurlingKernel r f x = czOperator beurlingKernel r f x * g x
    rw [mul_comm]
  -- Absolute integrability of `uncurry F` on `volume.prod volume`.
  have hintF : Integrable (Function.uncurry F) (volume.prod volume) := by
    -- The "diagonal-shifted" support set, measurable in the product.
    have hSmeas : MeasurableSet {z : ℂ × ℂ | r ≤ dist z.2 z.1} :=
      measurableSet_le measurable_const (continuous_snd.dist continuous_fst).measurable
    have huncEq : Function.uncurry F
        = {z : ℂ × ℂ | r ≤ dist z.2 z.1}.indicator
            (fun z => beurlingKernel z.1 z.2 * f z.1 * g z.2) := by
      funext z
      change (Metric.ball z.1 r)ᶜ.indicator (fun x => beurlingKernel z.1 x * f z.1 * g x) z.2
        = {z : ℂ × ℂ | r ≤ dist z.2 z.1}.indicator
            (fun z => beurlingKernel z.1 z.2 * f z.1 * g z.2) z
      by_cases h : z.2 ∈ (Metric.ball z.1 r)ᶜ
      · have hz : z ∈ {z : ℂ × ℂ | r ≤ dist z.2 z.1} := by
          simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt] at h
          rw [Set.mem_ofPred_eq]; exact h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem hz]
      · have hz : z ∉ {z : ℂ × ℂ | r ≤ dist z.2 z.1} := by
          simp only [Set.mem_compl_iff, Metric.mem_ball, not_not] at h
          rw [Set.mem_ofPred_eq, not_le]; exact h
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hz]
    have hmeasF : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
      rw [huncEq]
      apply AEStronglyMeasurable.indicator _ hSmeas
      apply AEStronglyMeasurable.mul
      · apply AEStronglyMeasurable.mul
        · apply Measurable.aestronglyMeasurable
          show Measurable (fun z : ℂ × ℂ => beurlingKernel z.1 z.2)
          unfold beurlingKernel; fun_prop
        · exact hf.aestronglyMeasurable.comp_fst
      · exact hg.aestronglyMeasurable.comp_snd
    rw [MeasureTheory.integrable_prod_iff hmeasF]
    constructor
    · -- a.e. `y`: `x ↦ F y x` integrable.
      filter_upwards with y
      change Integrable (fun x => (Metric.ball y r)ᶜ.indicator
        (fun x => beurlingKernel y x * f y * g x) x) volume
      rw [MeasureTheory.integrable_indicator_iff measurableSet_ball.compl]
      have hkg : IntegrableOn (fun x => beurlingKernel y x * g x) (Metric.ball y r)ᶜ volume :=
        integrableOn_beurlingKernel_mul_Lp (p := p') (p' := p) hr y hp'1 hp'_top hg
      have heq : (fun x => beurlingKernel y x * f y * g x)
          = (fun x => f y • (beurlingKernel y x * g x)) := by
        funext x; rw [smul_eq_mul]; ring
      rw [heq]
      exact (hkg.smul (f y))
    · -- `y ↦ ∫ x, ‖F y x‖` integrable, dominated by `Kr · ‖g‖_{p'} · ‖f y‖`.
      set Cg : ℝ≥0∞ := Kr * eLpNorm g p' volume with hCg_def
      have hCg_ne_top : Cg ≠ ⊤ := ENNReal.mul_ne_top hKr_ne_top hg.2.ne
      have hbd : ∀ y, ‖∫ x, ‖F y x‖ ∂volume‖ ≤ Cg.toReal * ‖f y‖ := by
        intro y
        have hnn : 0 ≤ ∫ x, ‖F y x‖ ∂volume := integral_nonneg (fun x => norm_nonneg _)
        rw [Real.norm_of_nonneg hnn]
        -- Express the real integral via its lintegral, then bound by Hölder.
        have hmeasFy : AEStronglyMeasurable (fun x => F y x) volume := by
          rw [hF_def]
          simp only
          apply AEStronglyMeasurable.indicator _ measurableSet_ball.compl
          apply AEStronglyMeasurable.mul _ (hg.aestronglyMeasurable)
          apply AEStronglyMeasurable.mul _ aestronglyMeasurable_const
          apply Measurable.aestronglyMeasurable
          unfold beurlingKernel; fun_prop
        have hle : (∫ x, ‖F y x‖ ∂volume) = (∫⁻ x, ‖F y x‖ₑ ∂volume).toReal :=
          integral_norm_eq_lintegral_enorm hmeasFy
        rw [hle]
        -- `∫⁻ x, ‖F y x‖ₑ = ‖f y‖ₑ · ∫⁻_{(ball y r)ᶜ} ‖K y x‖ₑ ‖g x‖ₑ`.
        have hlintEq : (∫⁻ x, ‖F y x‖ₑ ∂volume)
            = ‖f y‖ₑ * ∫⁻ x in (Metric.ball y r)ᶜ, ‖beurlingKernel y x‖ₑ * ‖g x‖ₑ := by
          rw [hF_def]
          simp only
          rw [show (fun x => ‖(Metric.ball y r)ᶜ.indicator
                (fun x => beurlingKernel y x * f y * g x) x‖ₑ)
              = (Metric.ball y r)ᶜ.indicator
                (fun x => ‖f y‖ₑ * (‖beurlingKernel y x‖ₑ * ‖g x‖ₑ)) from ?_]
          · rw [lintegral_indicator measurableSet_ball.compl, lintegral_const_mul']
            exact enorm_ne_top
          · funext x
            by_cases h : x ∈ (Metric.ball y r)ᶜ
            · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, enorm_mul, enorm_mul]; ring
            · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero]
        rw [hlintEq]
        -- Hölder: `∫⁻_{(ball y r)ᶜ} ‖K y x‖ₑ ‖g x‖ₑ ≤ Kr · ‖g‖_{p'}`.
        have hHolder : (∫⁻ x in (Metric.ball y r)ᶜ, ‖beurlingKernel y x‖ₑ * ‖g x‖ₑ) ≤ Cg := by
          have hcs := ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
            (μ := volume.restrict (Metric.ball y r)ᶜ) (p := p) (q := p')
            (ENNReal.HolderConjugate.symm)
            (f := fun x => ‖beurlingKernel y x‖ₑ) (g := fun x => ‖g x‖ₑ)
            (by unfold beurlingKernel; fun_prop) hg.aestronglyMeasurable.enorm.restrict
          simp only [eLpNorm_enorm] at hcs
          refine le_trans hcs ?_
          rw [hCg_def]
          refine mul_le_mul' ?_ (eLpNorm_restrict_le g p' volume _)
          refine le_trans ?_ (hkermem_p y)
          rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.compl]
        calc (‖f y‖ₑ * ∫⁻ x in (Metric.ball y r)ᶜ, ‖beurlingKernel y x‖ₑ * ‖g x‖ₑ).toReal
            ≤ (‖f y‖ₑ * Cg).toReal := by
              apply ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top hCg_ne_top)
              exact mul_le_mul' le_rfl hHolder
          _ = Cg.toReal * ‖f y‖ := by
              rw [ENNReal.toReal_mul, toReal_enorm, mul_comm]
      refine Integrable.mono' (g := fun y => Cg.toReal * ‖f y‖) ?_ ?_ ?_
      · exact (hfint.norm.const_mul Cg.toReal)
      · exact (hmeasF.norm).integral_prod_right'
      · filter_upwards with y; exact hbd y
  -- Fubini: swap the order of integration.
  have hswap : ∫ y, ∫ x, F y x = ∫ x, ∫ y, F y x :=
    MeasureTheory.integral_integral_swap hintF
  -- Conclude.
  calc ∫ x, czOperator beurlingKernel r f x * g x ∂volume
      = ∫ x, ∫ y, F y x := by simp_rw [hFx]
    _ = ∫ y, ∫ x, F y x := hswap.symm
    _ = ∫ x, f x * czOperator beurlingKernel r g x ∂volume := by simp_rw [hFy]

/-- **Truncation `Lᵖ` bound for `p > 2`, by duality.** Using `Lᵖ` duality, the
truncation symmetry, and the `Lᵖ'` truncation bound (`p' ∈ (1,2)`),
`‖czOp r f‖_p ≤ beurlingTruncLpConst p' · ‖f‖_p` for all `f ∈ Lᵖ` (first for
bounded-finite-support `f`, then by density). -/
lemma eLpNorm_czOperator_beurling_Lp_high {p p' : ℝ≥0∞} (hp2 : 2 < p) (hp_top : p ≠ ⊤)
    [ENNReal.HolderConjugate p p'] {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} (hf : MemLp f p volume) :
    eLpNorm (czOperator beurlingKernel r f) p volume
      ≤ (beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm f p volume := by
  have : ENNReal.HolderConjugate p' p := ENNReal.HolderConjugate.symm
  have hp1 : 1 < p := lt_trans (by norm_num) hp2
  have hp0 : p ≠ 0 := by rintro rfl; exact absurd hp1 (by simp)
  -- The conjugate exponent lies in `(1, 2)`.
  have hp'_top : p' ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr hp1).ne
  have hp'1 : 1 < p' :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp (lt_of_le_of_ne le_top hp_top)
  have hp'0 : p' ≠ 0 := (ENNReal.HolderConjugate.pos p' p).ne'
  -- `p' < 2` from `2 < p` via the real Hölder identity.
  have hq2real : (2:ℝ) < p.toReal := by
    rw [show (2:ℝ) = (2:ℝ≥0∞).toReal from by simp]
    exact (ENNReal.toReal_lt_toReal (by simp) hp_top).mpr hp2
  have hinvReal : (p.toReal)⁻¹ + (p'.toReal)⁻¹ = 1 := by
    have h := ENNReal.HolderConjugate.inv_add_inv_eq_one p p'
    have heq : (p⁻¹ + p'⁻¹).toReal = (1:ℝ≥0∞).toReal := by rw [h]
    rwa [ENNReal.toReal_add (by simp [hp0]) (by simp [hp'0]), ENNReal.toReal_inv,
      ENNReal.toReal_inv, ENNReal.toReal_one] at heq
  have hp'2 : p' < 2 := by
    have hp'pos : 0 < p'.toReal := ENNReal.toReal_pos hp'0 hp'_top
    have hlt : p'.toReal < 2 := by
      have hppos : 0 < p.toReal := by linarith
      have hainv : (p.toReal)⁻¹ < 2⁻¹ := by
        rw [inv_lt_inv₀ hppos (by norm_num)]; exact hq2real
      have hbinv : 2⁻¹ < (p'.toReal)⁻¹ := by
        have hb : (p'.toReal)⁻¹ = 1 - (p.toReal)⁻¹ := by linarith
        rw [hb]; norm_num; linarith [hainv]
      rwa [inv_lt_inv₀ (by norm_num) hp'pos] at hbinv
    rw [← ENNReal.toReal_lt_toReal hp'_top (by simp), show (2:ℝ≥0∞).toReal = 2 from by simp]
    exact hlt
  have hq_pos : (0:ℝ) < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hq_ge2 : (2:ℝ) ≤ p.toReal := by
    rw [show (2:ℝ) = (2:ℝ≥0∞).toReal from by simp]
    exact ENNReal.toReal_le_toReal (by simp) hp_top |>.mpr hp2.le
  -- **MemLp helper:** a function in `L² ∩ L∞` is in `Lᵖ` for `2 ≤ p < ∞`.
  have hLp_of_L2_Linf : ∀ h : ℂ → ℂ, MemLp h 2 volume → MemLp h ∞ volume → MemLp h p volume := by
    intro h h2 hinf
    refine ⟨h2.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp_top]
    set C : ℝ≥0∞ := eLpNormEssSup h volume with hC_def
    have hC_top : C ≠ ⊤ := by
      rw [hC_def, ← eLpNorm_exponent_top]; exact hinf.2.ne
    have hbd : ∀ᵐ x ∂volume, ‖h x‖ₑ ^ p.toReal ≤ C ^ (p.toReal - 2) * ‖h x‖ₑ ^ (2:ℝ) := by
      filter_upwards [ae_le_eLpNormEssSup (f := h) (μ := volume)] with x hx
      by_cases hzero : ‖h x‖ₑ = 0
      · rw [hzero, ENNReal.zero_rpow_of_pos hq_pos,
          ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2), mul_zero]
      · have hnn : (0:ℝ) ≤ p.toReal - 2 := by linarith
        have hxtop : ‖h x‖ₑ ≠ ⊤ := (hx.trans_lt (lt_top_iff_ne_top.mpr hC_top)).ne
        calc ‖h x‖ₑ ^ p.toReal
            = ‖h x‖ₑ ^ (p.toReal - 2) * ‖h x‖ₑ ^ (2:ℝ) := by
              rw [← ENNReal.rpow_add _ _ hzero hxtop]; ring_nf
          _ ≤ C ^ (p.toReal - 2) * ‖h x‖ₑ ^ (2:ℝ) :=
              mul_le_mul' (ENNReal.rpow_le_rpow hx hnn) le_rfl
    refine lt_of_le_of_lt (lintegral_mono_ae hbd) ?_
    rw [lintegral_const_mul' _ _ (by
      apply ENNReal.rpow_ne_top_of_nonneg (by linarith) hC_top)]
    have h2lint : (∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂volume) < ⊤ := by
      have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (μ := volume) (f := h) (p := 2) (by simp) (by simp)).mp h2.2
      simpa using this
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) hC_top)) h2lint
  -- **Hölder pairing bound:** `‖∫ a·b‖ₑ ≤ eLpNorm a p · eLpNorm b p'`.
  have hPairing : ∀ a b : ℂ → ℂ, AEStronglyMeasurable a volume → AEStronglyMeasurable b volume →
      ‖∫ x, a x * b x ∂volume‖ₑ ≤ eLpNorm a p volume * eLpNorm b p' volume := by
    intro a b ha hb
    calc ‖∫ x, a x * b x ∂volume‖ₑ
        ≤ ∫⁻ x, ‖a x * b x‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ x, ‖a x‖ₑ * ‖b x‖ₑ ∂volume := by simp_rw [enorm_mul]
      _ ≤ eLpNorm a p volume * eLpNorm b p' volume := by
          have := ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
            (μ := volume) (p := p) (q := p') inferInstance
            (f := fun x => ‖a x‖ₑ) (g := fun x => ‖b x‖ₑ) ha.enorm hb.enorm
          simpa [eLpNorm_enorm] using this
  -- **Part (a): the bound for `BoundedFiniteSupport` `f`.**
  have hBFS : ∀ h : ℂ → ℂ, BoundedFiniteSupport h volume →
      eLpNorm (czOperator beurlingKernel r h) p volume
        ≤ (beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm h p volume := by
    intro h hh
    have hhLp : MemLp h p volume := hh.memLp p
    -- `czOp r h ∈ L² ∩ L∞ ⊆ Lᵖ`.
    have hczL2 : MemLp (czOperator beurlingKernel r h) 2 volume :=
      ⟨aestronglyMeasurable_czOperator_beurling (hh.memLp 2),
        lt_of_le_of_lt (eLpNorm_czOperator_beurling_L2 hr (hh.memLp 2))
          (ENNReal.mul_lt_top (by finiteness) (hh.memLp 2).2)⟩
    -- The `L¹` operator enorm bound: `‖czOp r h x‖ₑ ≤ ofReal(r⁻²)·‖h‖₁`.
    have hOpBoundE : ∀ x : ℂ, ‖czOperator beurlingKernel r h x‖ₑ
        ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm h 1 volume := by
      intro x
      have hkernelEnorm : ∀ y ∈ (Metric.ball x r)ᶜ,
          ‖beurlingKernel x y‖ₑ ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) := by
        intro y hy
        have hr_le : r ≤ ‖x - y‖ := by
          rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_comm] at hy
          rw [Complex.dist_eq] at hy; exact hy
        have hxy_pos : 0 < ‖x - y‖ := lt_of_lt_of_le hr hr_le
        have hnorm : ‖beurlingKernel x y‖ = ‖x - y‖ ^ (-2 : ℤ) := by
          rw [beurlingKernel, norm_zpow]
        have hle : ‖beurlingKernel x y‖ ≤ (r : ℝ) ^ (-2 : ℤ) := by
          rw [hnorm, zpow_neg, zpow_neg, zpow_two, zpow_two]
          exact inv_anti₀ (by positivity) (mul_le_mul hr_le hr_le hr.le hxy_pos.le)
        calc ‖beurlingKernel x y‖ₑ = ENNReal.ofReal ‖beurlingKernel x y‖ :=
              (ofReal_norm _).symm
          _ ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) := ENNReal.ofReal_le_ofReal hle
      have hczeq : czOperator beurlingKernel r h x
          = ∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * h y := rfl
      rw [hczeq]
      calc ‖∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * h y‖ₑ
          ≤ ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y * h y‖ₑ :=
            enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y‖ₑ * ‖h y‖ₑ := by simp_rw [enorm_mul]
        _ ≤ ∫⁻ y in (Metric.ball x r)ᶜ, ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * ‖h y‖ₑ := by
            exact setLIntegral_mono' measurableSet_ball.compl
              (fun y hy => mul_le_mul' (hkernelEnorm y hy) le_rfl)
        _ = ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ))
              * ∫⁻ y in (Metric.ball x r)ᶜ, ‖h y‖ₑ := by rw [lintegral_const_mul']; finiteness
        _ ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * ∫⁻ y, ‖h y‖ₑ :=
            mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
        _ = ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm h 1 volume := by
            rw [eLpNorm_one_eq_lintegral_enorm]
    have hczLinf : MemLp (czOperator beurlingKernel r h) ∞ volume := by
      set M : ℝ := (r : ℝ) ^ (-2 : ℤ) * (eLpNorm h 1 volume).toReal with hM_def
      refine memLp_top_of_bound
        (aestronglyMeasurable_czOperator_beurling' hhLp.aestronglyMeasurable) M ?_
      filter_upwards with x
      have hbE := hOpBoundE x
      rw [← ofReal_norm] at hbE
      have hh1 : eLpNorm h 1 volume ≠ ⊤ := (hh.memLp 1).2.ne
      have hprod : ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm h 1 volume
          = ENNReal.ofReal M := by
        rw [hM_def, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hh1]
      rw [hprod] at hbE
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbE
    have hczLp : MemLp (czOperator beurlingKernel r h) p volume :=
      hLp_of_L2_Linf _ hczL2 hczLinf
    -- Duality: bound `‖czOp r h‖_p` by the supremum of the pairing.
    refine le_trans (eLpNorm_le_iSup_integral_mul (p' := p') hp1 hp_top hczLp) ?_
    refine iSup_le (fun g => iSup_le (fun hgmem => iSup_le (fun hgle => ?_)))
    -- Pairing symmetry + Hölder + `Lᵖ'` truncation bound.
    calc ‖∫ x, czOperator beurlingKernel r h x * g x ∂volume‖ₑ
        = ‖∫ x, h x * czOperator beurlingKernel r g x ∂volume‖ₑ := by
          rw [czOperator_beurling_pairing_symm hp1 hp_top hr hh hgmem]
      _ ≤ eLpNorm h p volume * eLpNorm (czOperator beurlingKernel r g) p' volume :=
          hPairing h (czOperator beurlingKernel r g) hhLp.aestronglyMeasurable
            (aestronglyMeasurable_czOperator_beurling' hgmem.aestronglyMeasurable)
      _ ≤ eLpNorm h p volume * ((beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm g p' volume) :=
          mul_le_mul' le_rfl (eLpNorm_czOperator_beurling_Lp hp'1 hp'2 hr hgmem)
      _ ≤ eLpNorm h p volume * ((beurlingTruncLpConst p' : ℝ≥0∞) * 1) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hgle)
      _ = (beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm h p volume := by
          rw [mul_one, mul_comm]
  -- **Part (b): density extension to all of `Lᵖ`.**
  have hp1' : (1:ℝ≥0∞) ≤ p := hp1.le
  -- Smooth compactly-supported `Lᵖ`-approximating sequence (`BoundedFiniteSupport`).
  choose gg hggc hggsmooth hggle using fun n : ℕ =>
    hf.exist_eLpNorm_sub_le hp_top hp1' (ε := 1/(n+1)) (by positivity)
  have hggmem : ∀ n, MemLp (gg n) p volume := fun n =>
    (hggsmooth n).continuous.memLp_of_hasCompactSupport (hggc n)
  have hggBFS : ∀ n, BoundedFiniteSupport (gg n) volume := fun n =>
    boundedFiniteSupport_of_contDiff (hggsmooth n) (hggc n)
  have htend : Tendsto (fun n => eLpNorm (f - gg n) p volume) atTop (𝓝 0) := by
    have hto0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1))) atTop (𝓝 0) := by
      rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
      (fun n => zero_le) hggle
  -- The kernel section centered at `x` is in `Lᵖ'` (`∫_{|u|≥r}|u|^{-2 p'.toReal} < ∞`).
  set q' : ℝ := p'.toReal with hq'_def
  have hq'1 : 1 < q' := by
    rw [hq'_def, show (1:ℝ) = (1 : ℝ≥0∞).toReal from rfl]
    exact ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp'_top |>.mpr hp'1
  have hq'0 : 0 < q' := lt_trans one_pos hq'1
  have hlint' : ∫⁻ u : ℂ in {u : ℂ | r ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q' < ⊤ := by
    rw [← lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
      ← Complex.lintegral_comp_polarCoord_symm]
    set box : ℝ × ℝ → ENNReal := fun p =>
      (Set.Ici r ×ˢ Set.Ioo (-π) π).indicator
        (fun p => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) p with hbox
    have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.mul measurable_fst
      exact (Real.continuous_rpow_const hq'0.le).measurable.comp ((measurable_fst.pow_const 2).inv)
    have hbound : ∀ pp ∈ polarCoord.target,
        ENNReal.ofReal pp.1 • {u : ℂ | r ≤ ‖u‖}.indicator
          (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (Complex.polarCoord.symm pp) ≤ box pp := by
      intro pp hpp
      rw [polarCoord_target, Set.mem_prod] at hpp
      obtain ⟨hpp1, hpp2⟩ := hpp
      simp only [Set.mem_Ioi] at hpp1
      simp only [hbox]
      have hnorm : ‖Complex.polarCoord.symm pp‖ = pp.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hpp1]
      by_cases hmem : Complex.polarCoord.symm pp ∈ {u : ℂ | r ≤ ‖u‖}
      · have hpR : r ≤ pp.1 := by rw [Set.mem_ofPred_eq, hnorm] at hmem; exact hmem
        rw [Set.indicator_of_mem hmem,
          Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hpR, hpp2⟩)]
        have henorm : ‖Complex.polarCoord.symm pp‖ₑ = ENNReal.ofReal pp.1 := by
          rw [← ofReal_norm, hnorm]
        rw [henorm, smul_eq_mul,
          show ((ENNReal.ofReal pp.1 ^ 2)⁻¹) ^ q' = ENNReal.ofReal (((pp.1^2)⁻¹)^q') by
            rw [← ENNReal.ofReal_pow hpp1.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
              ENNReal.ofReal_rpow_of_pos (by positivity)],
          ← ENNReal.ofReal_mul hpp1.le]
      · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le
    refine lt_of_le_of_lt (setLIntegral_mono
      (hmeas_polar.indicator (measurableSet_Ici.prod measurableSet_Ioo)) hbound) ?_
    calc ∫⁻ pp in polarCoord.target, box pp
        ≤ ∫⁻ pp, box pp := setLIntegral_le_lintegral _ _
      _ = ∫⁻ pp in (Set.Ici r ×ˢ Set.Ioo (-π) π), ENNReal.ofReal (pp.1 * ((pp.1^2)⁻¹)^q') := by
            rw [hbox, lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hmeas_polar.aemeasurable]
            simp only [setLIntegral_const]
            rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
            apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
            have hint : IntegrableOn (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q') (Set.Ici r) volume := by
              have heq : (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q')
                  =ᶠ[ae (volume.restrict (Set.Ici r))]
                  (fun ρ : ℝ => ρ^(1 - 2 * q')) := by
                filter_upwards [ae_restrict_mem measurableSet_Ici] with ρ hρ
                simp only [Set.mem_Ici] at hρ
                have hρpos : 0 < ρ := lt_of_lt_of_le hr hρ
                have hbase : (ρ^2)⁻¹ = ρ^(-2 : ℝ) := by
                  rw [Real.rpow_neg hρpos.le, ← Real.rpow_natCast ρ 2]; norm_num
                have h1 : ((ρ^2)⁻¹)^q' = ρ^(-2 * q') := by
                  rw [hbase, ← Real.rpow_mul hρpos.le]
                have h2 : ρ * ρ^(-2 * q') = ρ^(1 - 2 * q') := by
                  nth_rewrite 1 [← Real.rpow_one ρ]
                  rw [← Real.rpow_add hρpos]; congr 1; ring
                rw [h1, h2]
              rw [integrableOn_congr_fun_ae heq, integrableOn_Ici_iff_integrableOn_Ioi,
                integrableOn_Ioi_rpow_iff hr]
              nlinarith [hq'1]
            have hfin := hint.2
            rw [hasFiniteIntegral_iff_enorm] at hfin
            refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y hy => ?_)) hfin
            · refine (measurable_id.mul ?_).enorm
              exact (Real.continuous_rpow_const hq'0.le).measurable.comp
                ((measurable_id.pow_const 2).inv)
            · simp only [Set.mem_Ici] at hy
              have hypos : 0 < y := lt_of_lt_of_le hr hy
              rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hkersec : ∀ x : ℂ, MemLp
      (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) p' volume := by
    intro x
    have hmeas : AEStronglyMeasurable
        (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) volume := by
      apply AEStronglyMeasurable.indicator _ measurableSet_ball.compl
      apply Measurable.aestronglyMeasurable
      unfold beurlingKernel; fun_prop
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp'0 hp'_top, ← hq'_def]
    have hpt : ∀ y, ‖(Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y‖ₑ ^ q'
        = (Metric.ball x r)ᶜ.indicator (fun y => ‖beurlingKernel x y‖ₑ ^ q') y := by
      intro y
      by_cases h : y ∈ (Metric.ball x r)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero,
          ENNReal.zero_rpow_of_pos hq'0]
    refine lt_of_eq_of_lt (lintegral_congr hpt) ?_
    rw [lintegral_indicator measurableSet_ball.compl]
    have hkb : ∀ y, ‖beurlingKernel x y‖ₑ ^ q' ≤ ((‖x - y‖ₑ ^ 2)⁻¹) ^ q' := by
      intro y
      apply ENNReal.rpow_le_rpow _ hq'0.le
      by_cases h : x = y
      · subst h; simp [beurlingKernel]
      · have hne : x - y ≠ 0 := sub_ne_zero.mpr h
        have he : beurlingKernel x y = ((x-y) * (x-y))⁻¹ := by
          rw [beurlingKernel, zpow_neg, zpow_two]
        rw [he, enorm_inv (mul_ne_zero hne hne), enorm_mul, sq]
    refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y _ => hkb y)) ?_
    · exact ENNReal.continuous_rpow_const.measurable.comp
        ((((measurable_const.sub measurable_id).enorm).pow_const 2).inv)
    rw [← lintegral_indicator measurableSet_ball.compl]
    have hsub : (fun y => (Metric.ball x r)ᶜ.indicator (fun y => ((‖x - y‖ₑ ^ 2)⁻¹) ^ q') y)
        = (fun y => {u : ℂ | r ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (x - y)) := by
      funext y
      have hiff : (y ∈ (Metric.ball x r)ᶜ) ↔ (x - y ∈ {u : ℂ | r ≤ ‖u‖}) := by
        rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_ofPred_eq, dist_comm,
          Complex.dist_eq]
      by_cases h : y ∈ (Metric.ball x r)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
    rw [hsub, lintegral_sub_left_eq_self
      (fun u => {u : ℂ | r ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') u) x]
    rw [lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable)]
    exact hlint'
  -- Per-point Hölder bound: `‖czOp r u x‖ₑ ≤ ‖kernel section_x‖_{p'} · ‖u‖_p`.
  have hHolderPt : ∀ (x : ℂ) {u : ℂ → ℂ}, MemLp u p volume →
      ‖czOperator beurlingKernel r u x‖ₑ
        ≤ eLpNorm (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) p'
            volume * eLpNorm u p volume := by
    intro x u hu
    have hcs : ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y‖ₑ * ‖u y‖ₑ
        ≤ eLpNorm (fun y => beurlingKernel x y) p' (volume.restrict (Metric.ball x r)ᶜ)
          * eLpNorm u p (volume.restrict (Metric.ball x r)ᶜ) := by
      have := ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
        (μ := volume.restrict (Metric.ball x r)ᶜ) (p := p') (q := p) (ENNReal.HolderConjugate.symm)
        (f := fun y => ‖beurlingKernel x y‖ₑ) (g := fun y => ‖u y‖ₑ)
        (by unfold beurlingKernel; fun_prop) hu.aestronglyMeasurable.enorm.restrict
      simpa [eLpNorm_enorm] using this
    have hczeq : czOperator beurlingKernel r u x
        = ∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * u y := rfl
    rw [hczeq]
    calc ‖∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * u y‖ₑ
        ≤ ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y * u y‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y‖ₑ * ‖u y‖ₑ := by simp_rw [enorm_mul]
      _ ≤ eLpNorm (fun y => beurlingKernel x y) p' (volume.restrict (Metric.ball x r)ᶜ)
            * eLpNorm u p (volume.restrict (Metric.ball x r)ᶜ) := hcs
      _ ≤ eLpNorm (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) p'
              volume * eLpNorm u p volume :=
          mul_le_mul'
            (le_of_eq (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.compl).symm)
            (eLpNorm_restrict_le u p volume _)
  -- `czOp r (gg n) x → czOp r f x` for every `x` (uniform Hölder bound on the difference).
  have hconv : ∀ x : ℂ, Tendsto (fun n => czOperator beurlingKernel r (gg n) x) atTop
      (𝓝 (czOperator beurlingKernel r f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    set C := eLpNorm
      (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) p' volume with hCdef
    have hCne : C ≠ ⊤ := by rw [hCdef]; exact (hkersec x).2.ne
    -- The enorm difference `→ 0`.
    have hbdE : ∀ n, ‖czOperator beurlingKernel r (gg n) x - czOperator beurlingKernel r f x‖ₑ
        ≤ C * eLpNorm (gg n - f) p volume := by
      intro n
      rw [← czOperator_beurling_sub_Lp hp1 hp_top hr x (hggmem n) hf]
      exact hHolderPt x ((hggmem n).sub hf)
    have hRHS0 : Tendsto (fun n => C * eLpNorm (gg n - f) p volume) atTop (𝓝 0) := by
      have heq : ∀ n, eLpNorm (gg n - f) p volume = eLpNorm (f - gg n) p volume := by
        intro n; rw [← eLpNorm_neg]; congr 1; funext y; simp
      have : Tendsto (fun n => C * eLpNorm (f - gg n) p volume) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul htend (Or.inr hCne)
      exact this.congr (fun n => by rw [heq n])
    have henorm0 : Tendsto
        (fun n => ‖czOperator beurlingKernel r (gg n) x - czOperator beurlingKernel r f x‖ₑ)
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRHS0
        (fun n => zero_le) hbdE
    have := (ENNReal.tendsto_toReal (by simp)).comp henorm0
    simpa [Function.comp_def, toReal_enorm] using this
  -- Fatou: pass the BFS bound `eLpNorm (czOp r (gg n)) p ≤ C_{p'} · ‖gg n‖_p` to the limit.
  have hggnorm : Tendsto (fun n => eLpNorm (gg n) p volume) atTop (𝓝 (eLpNorm f p volume)) := by
    set L := eLpNorm f p volume with hL
    set d := fun n => eLpNorm (f - gg n) p volume with hd
    have hupper : ∀ n, eLpNorm (gg n) p volume ≤ L + d n := by
      intro n
      have h : eLpNorm (gg n) p volume ≤ eLpNorm f p volume + eLpNorm (gg n - f) p volume := by
        calc eLpNorm (gg n) p volume = eLpNorm (f + (gg n - f)) p volume := by
              congr 1; funext y; simp
          _ ≤ eLpNorm f p volume + eLpNorm (gg n - f) p volume :=
              eLpNorm_add_le hf.aestronglyMeasurable
                ((hggmem n).sub hf).aestronglyMeasurable hp1'
      rw [hL, hd]
      rwa [show eLpNorm (gg n - f) p volume = eLpNorm (f - gg n) p volume from by
        rw [← eLpNorm_neg]; congr 1; funext y; simp] at h
    have hlower : ∀ n, L - d n ≤ eLpNorm (gg n) p volume := by
      intro n
      rw [tsub_le_iff_right]
      calc L = eLpNorm ((gg n) + (f - gg n)) p volume := by rw [hL]; congr 1; funext y; simp
        _ ≤ eLpNorm (gg n) p volume + eLpNorm (f - gg n) p volume :=
            eLpNorm_add_le (hggmem n).aestronglyMeasurable
              (hf.sub (hggmem n)).aestronglyMeasurable hp1'
    have hupper' : Tendsto (fun n => L + d n) atTop (𝓝 L) := by
      simpa using tendsto_const_nhds.add htend
    have hlower' : Tendsto (fun n => L - d n) atTop (𝓝 L) := by
      simpa using (ENNReal.Tendsto.sub (a := L) (b := 0) tendsto_const_nhds htend
        (Or.inr (by simp)))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower' hupper' hlower hupper
  have hCfin : Tendsto (fun n => (beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm (gg n) p volume) atTop
      (𝓝 ((beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm f p volume)) :=
    ENNReal.Tendsto.const_mul hggnorm (Or.inr ENNReal.coe_ne_top)
  -- The BFS bound holds for each `gg n`.
  have hggbd : ∀ n, eLpNorm (czOperator beurlingKernel r (gg n)) p volume
      ≤ (beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm (gg n) p volume :=
    fun n => hBFS (gg n) (hggBFS n)
  -- Pass to the limit by Fatou via the `ε`-route.
  set K := (beurlingTruncLpConst p' : ℝ≥0∞) * eLpNorm f p volume with hKdef
  have hKfin : K < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  have hKlt : K < K + (ε : ℝ≥0∞) := ENNReal.lt_add_right hKfin.ne (by exact_mod_cast hε.ne')
  have hbound : ∀ᶠ n in atTop,
      eLpNorm (czOperator beurlingKernel r (gg n)) p volume ≤ K + (ε : ℝ≥0∞) := by
    have hev := hCfin.eventually_le_const hKlt
    filter_upwards [hev] with n hn
    exact le_trans (hggbd n) hn
  exact Lp.eLpNorm_le_of_ae_tendsto hbound
    (fun n => aestronglyMeasurable_czOperator_beurling' (hggmem n).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => hconv x))

/-- **Maximal-operator `Lᵖ` bound for `p > 2`** (the `p < 2` replication
`exists_eLpNorm_simpleNontangential_beurling_Lp` with the duality truncation bound
`eLpNorm_czOperator_beurling_Lp_high`). -/
lemma exists_eLpNorm_simpleNontangential_beurling_Lp_high {p : ℝ≥0∞} (hp2 : 2 < p)
    (hp_top : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∀ g : ℂ → ℂ, MemLp g p volume →
      eLpNorm (simpleNontangentialOperator beurlingKernel 0 g) p volume
        ≤ (C : ℝ≥0∞) * eLpNorm g p volume := by
  have hp1 : 1 < p := lt_trans (by norm_num : (1:ℝ≥0∞) < 2) hp2
  have hp1' : (1 : ℝ≥0∞) ≤ p := hp1.le
  -- The conjugate exponent `p' = (1 - p⁻¹)⁻¹` and its `HolderConjugate` instance,
  -- needed for the duality (`p > 2`) truncation bound `eLpNorm_czOperator_beurling_Lp_high`.
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hp'_def
  have hpinv_le_one : p⁻¹ ≤ 1 := by rw [ENNReal.inv_le_one]; exact hp1.le
  have hHC : ENNReal.HolderConjugate p p' := by
    rw [hp'_def, ENNReal.holderConjugate_iff, inv_inv, add_tsub_cancel_of_le hpinv_le_one]
  -- `p` as an `ℝ≥0`, with `1 < pnn`.
  set pnn : ℝ≥0 := p.toNNReal with hpnn_def
  have hpnn_coe : (pnn : ℝ≥0∞) = p := by rw [hpnn_def, ENNReal.coe_toNNReal hp_top]
  have hpnn1 : 1 < pnn := by
    have : (1 : ℝ≥0∞) < (pnn : ℝ≥0∞) := by rw [hpnn_coe]; exact hp1
    exact_mod_cast this
  -- The HL maximal `Lᵖ` strong-type bound (constant `Cgmf`).
  -- Use the `defaultA 4` doubling structure (the one carried by the Carleson lemmas).
  have hA4 : (volume : Measure ℂ).IsDoubling ((defaultA 4 : ℕ) : ℝ≥0) :=
    doublingMeasure_complex_defaultA4.toIsDoubling
  set Cgmf : ℝ≥0 := C2_0_6 ((defaultA 4 : ℕ) : ℝ≥0) 1 pnn with hCgmf_def
  have hgmf : HasStrongType
      (globalMaximalFunction (X := ℂ) (ε := ℂ) volume 1)
      (pnn : ℝ≥0∞) (pnn : ℝ≥0∞) volume volume Cgmf := by
    have h := hasStrongType_maximalFunction (X := ℂ) (ε' := ℂ) (μ := volume)
      (A := ((defaultA 4 : ℕ) : ℝ≥0)) (𝓑 := Set.univ (α := ℂ × ℝ)) (c := (·.fst))
      (r := (·.snd)) (p₁ := 1) (p₂ := pnn) zero_lt_one hpnn1
    norm_cast at h
  -- Abbreviations for the truncation constant (the duality constant `beurlingTruncLpConst p'`).
  set Ctr : ℝ≥0 := beurlingTruncLpConst p' with hCtr_def
  -- **Part (a): the BFS bound at a positive scale `r`.**
  set C₀ : ℝ≥0 := 4 * Cgmf * Ctr + (C10_1_5 4 + C10_1_2 4) * Cgmf with hC₀_def
  have hBFSscale : ∀ {r : ℝ}, 0 < r → ∀ g : ℂ → ℂ, BoundedFiniteSupport g volume →
      eLpNorm (simpleNontangentialOperator beurlingKernel r g) p volume
        ≤ (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
    intro r hr g hg
    -- The strong-type input for Cotlar's estimate (`L²` truncation bound).
    have hT : ∀ s > 0, HasBoundedStrongType (czOperator beurlingKernel s) 2 2 volume volume
        (C_Ts 4 : ℝ≥0∞) := fun s hs => czOperator_beurling_strongType_L2 hs
    -- The pointwise dominating function (Cotlar + x-shift), exponent-free.
    set pointwise : ℂ → ℝ≥0∞ :=
      4 * globalMaximalFunction volume 1 (czOperator beurlingKernel r g)
        + C10_1_5 4 • globalMaximalFunction volume 1 g
        + C10_1_2 4 • globalMaximalFunction volume 1 g with hpw_def
    -- Pointwise domination (verbatim from `simple_nontangential_operator`).
    have hdom : ∀ x, simpleNontangentialOperator beurlingKernel r g x ≤ pointwise x := by
      simp_rw [hpw_def, simpleNontangentialOperator, iSup_le_iff]
      intro x R hR x' hx'
      rw [Metric.mem_ball, dist_comm] at hx'
      trans ‖czOperator beurlingKernel R g x‖ₑ
          + C10_1_2 4 * globalMaximalFunction volume 1 g x
      · calc ‖czOperator beurlingKernel R g x'‖ₑ
            = ‖czOperator beurlingKernel R g x
              + (czOperator beurlingKernel R g x' - czOperator beurlingKernel R g x)‖ₑ := by
              congr 1; ring
          _ ≤ ‖czOperator beurlingKernel R g x‖ₑ
              + ‖czOperator beurlingKernel R g x'
                - czOperator beurlingKernel R g x‖ₑ := enorm_add_le _ _
          _ ≤ ‖czOperator beurlingKernel R g x‖ₑ
              + C10_1_2 4 * globalMaximalFunction volume 1 g x := by
              gcongr
              rw [← edist_eq_enorm_sub, edist_comm]
              exact estimate_x_shift (K := beurlingKernel) (by norm_num) hg
                (hr.trans hR.lt) hx'.le
      · refine add_le_add (cotlar_estimate (K := beurlingKernel) (r := r) (R := R)
          (by norm_num) hT hg ?_) (by rfl) |>.trans ?_
        · rw [Set.mem_Ioc]; exact ⟨hr, hR.le⟩
        · apply le_of_eq
          simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, ENNReal.smul_def, smul_eq_mul,
            Pi.ofNat_apply, add_assoc]
    -- Take `eLpNorm _ p` and use the additivity + maximal `Lᵖ` + truncation `Lᵖ` bounds.
    refine (eLpNorm_mono_enorm (g := pointwise) (fun x => by
      simp only [enorm_eq_self]; exact hdom x)).trans ?_
    -- `czOperator r g ∈ Lᵖ` and `g ∈ Lᵖ` (from `BoundedFiniteSupport`).
    have hgLp : MemLp g p volume := hg.memLp p
    have hczLp : MemLp (czOperator beurlingKernel r g) p volume := by
      refine ⟨aestronglyMeasurable_czOperator_beurling' hgLp.aestronglyMeasurable, ?_⟩
      exact lt_of_le_of_lt (eLpNorm_czOperator_beurling_Lp_high (p' := p') hp2 hp_top hr hgLp)
        (ENNReal.mul_lt_top ENNReal.coe_lt_top hgLp.2)
    -- Strong-type bounds for the maximal functions.
    have hgmf_g := (hgmf g (by rw [hpnn_coe]; exact hgLp)).2
    have hgmf_czg := (hgmf (czOperator beurlingKernel r g) (by rw [hpnn_coe]; exact hczLp)).2
    rw [hpnn_coe] at hgmf_g hgmf_czg
    -- Measurability for `eLpNorm_add_le`.
    have hm_czg : AEStronglyMeasurable
        (globalMaximalFunction volume 1 (czOperator beurlingKernel r g)) volume :=
      measurable_maximalFunction.aestronglyMeasurable
    have hm_g : AEStronglyMeasurable (globalMaximalFunction volume 1 g) volume :=
      measurable_maximalFunction.aestronglyMeasurable
    rw [hpw_def, show (4 : ℂ → ℝ≥0∞)
          * globalMaximalFunction volume 1 (czOperator beurlingKernel r g)
        = (4 : ℝ≥0) • globalMaximalFunction volume 1 (czOperator beurlingKernel r g) by
      ext y; simp [ENNReal.smul_def]]
    -- Split the eLpNorm of the sum.
    refine (eLpNorm_add_le (by fun_prop) (by fun_prop) hp1').trans ?_
    refine (add_le_add (eLpNorm_add_le (by fun_prop) (by fun_prop) hp1') (le_refl _)).trans ?_
    rw [show eLpNorm ((4 : ℝ≥0) • globalMaximalFunction volume 1
          (czOperator beurlingKernel r g)) p volume
        = ‖(4 : ℝ≥0)‖ₑ * eLpNorm (globalMaximalFunction volume 1
          (czOperator beurlingKernel r g)) p volume from eLpNorm_const_smul',
      show eLpNorm (C10_1_5 4 • globalMaximalFunction volume 1 g) p volume
        = ‖C10_1_5 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
        from eLpNorm_const_smul',
      show eLpNorm (C10_1_2 4 • globalMaximalFunction volume 1 g) p volume
        = ‖C10_1_2 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
        from eLpNorm_const_smul']
    -- Apply the maximal `Lᵖ` bound and then the truncation `Lᵖ` bound.
    have hkey : ‖(4 : ℝ≥0)‖ₑ * eLpNorm (globalMaximalFunction volume 1
          (czOperator beurlingKernel r g)) p volume
        + (‖C10_1_5 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
          + ‖C10_1_2 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume)
        ≤ (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
      have hb1 : eLpNorm (globalMaximalFunction volume 1 (czOperator beurlingKernel r g)) p volume
          ≤ (Cgmf : ℝ≥0∞) * ((Ctr : ℝ≥0∞) * eLpNorm g p volume) := by
        refine hgmf_czg.trans ?_
        rw [hCtr_def]
        exact mul_le_mul' (le_refl _)
          (eLpNorm_czOperator_beurling_Lp_high (p' := p') hp2 hp_top hr hgLp)
      have hb2 : eLpNorm (globalMaximalFunction volume 1 g) p volume
          ≤ (Cgmf : ℝ≥0∞) * eLpNorm g p volume := hgmf_g
      calc ‖(4 : ℝ≥0)‖ₑ * eLpNorm (globalMaximalFunction volume 1
              (czOperator beurlingKernel r g)) p volume
            + (‖C10_1_5 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
              + ‖C10_1_2 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume)
          ≤ ‖(4 : ℝ≥0)‖ₑ * ((Cgmf : ℝ≥0∞) * ((Ctr : ℝ≥0∞) * eLpNorm g p volume))
              + (‖C10_1_5 4‖ₑ * ((Cgmf : ℝ≥0∞) * eLpNorm g p volume)
                + ‖C10_1_2 4‖ₑ * ((Cgmf : ℝ≥0∞) * eLpNorm g p volume)) := by
            gcongr
        _ = (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
            rw [hC₀_def]
            push_cast [enorm_NNReal]
            ring
    rw [add_assoc]; exact hkey
  -- **Scale-0 BFS bound** (monotone convergence over `r = (n+1)⁻¹`).
  have hBFS0 : ∀ g : ℂ → ℂ, BoundedFiniteSupport g volume →
      eLpNorm (simpleNontangentialOperator beurlingKernel 0 g) p volume
        ≤ (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
    intro g hg
    set fseq : ℕ → ℂ → ℝ≥0∞ :=
      fun n => simpleNontangentialOperator beurlingKernel (n + 1 : ℝ)⁻¹ g with hfseq_def
    have f_mon : ∀ x : ℂ, Monotone fun n => fseq n x := by
      intro x m n hmn
      simp only [hfseq_def, simpleNontangentialOperator]
      gcongr with R
      apply iSup_const_mono (lt_of_le_of_lt _)
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      simp only [add_le_add_iff_right]
      exact_mod_cast hmn
    have snt0 : ⨆ (n : ℕ), fseq n = simpleNontangentialOperator beurlingKernel 0 g := by
      ext x
      simp only [hfseq_def]
      simp_rw [iSup_apply, simpleNontangentialOperator, gt_iff_lt]
      rw [iSup_comm]
      congr 1; ext R
      apply le_antisymm (iSup_le <| fun n => iSup_const_mono (lt_trans (by positivity)))
        (iSup_le _)
      intro hR
      set n := Nat.ceil R⁻¹ with hn_def
      have hn : (n + 1 : ℝ)⁻¹ < R :=
        inv_lt_of_inv_lt₀ hR <| (Nat.le_ceil R⁻¹).trans_lt (by exact_mod_cast lt_add_one _)
      refine le_iSup_of_le n ?_
      rw [iSup_pos hn]
    have mct := eLpNorm_iSup' (p := p) (f := fseq) (μ := volume)
      (fun n => aestronglyMeasurable_simpleNontangentialOperator.aemeasurable)
      (by filter_upwards; exact f_mon)
    rw [← snt0, show (⨆ n, fseq n) = fun x => ⨆ n, fseq n x from funext fun _ => iSup_apply, mct]
    apply iSup_le
    intro n
    exact hBFSscale (r := (n + 1 : ℝ)⁻¹) (by positivity) g hg
  -- **Part (b): extend the scale-0 bound from `BoundedFiniteSupport` to all of `Lᵖ`.**
  -- Per-point Hölder bound for the truncation against an `Lᵖ` function.
  have hHolderPt : ∀ (R : ℝ), 0 < R → ∀ (x' : ℂ) {h : ℂ → ℂ}, MemLp h p volume →
      ‖czOperator beurlingKernel R h x'‖ₑ
        ≤ eLpNorm (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p'
            volume * eLpNorm h p volume := by
    intro R hR x' h hh
    unfold czOperator
    have hcs : ∫⁻ y in (Metric.ball x' R)ᶜ, ‖beurlingKernel x' y‖ₑ * ‖h y‖ₑ
        ≤ eLpNorm (fun y => beurlingKernel x' y) p' (volume.restrict (Metric.ball x' R)ᶜ)
          * eLpNorm h p (volume.restrict (Metric.ball x' R)ᶜ) := by
      have := ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
        (μ := volume.restrict (Metric.ball x' R)ᶜ) (p := p') (q := p)
        (ENNReal.HolderConjugate.symm)
        (f := fun y => ‖beurlingKernel x' y‖ₑ) (g := fun y => ‖h y‖ₑ)
        (by unfold beurlingKernel; fun_prop) hh.aestronglyMeasurable.enorm.restrict
      simpa [eLpNorm_enorm] using this
    calc ‖∫ y in (Metric.ball x' R)ᶜ, beurlingKernel x' y * h y‖ₑ
        ≤ ∫⁻ y in (Metric.ball x' R)ᶜ, ‖beurlingKernel x' y * h y‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y in (Metric.ball x' R)ᶜ, ‖beurlingKernel x' y‖ₑ * ‖h y‖ₑ := by simp_rw [enorm_mul]
      _ ≤ eLpNorm (fun y => beurlingKernel x' y) p' (volume.restrict (Metric.ball x' R)ᶜ)
            * eLpNorm h p (volume.restrict (Metric.ball x' R)ᶜ) := hcs
      _ ≤ eLpNorm (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p'
              volume * eLpNorm h p volume := by
          refine mul_le_mul' ?_ ?_
          · exact le_of_eq (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.compl).symm
          · exact eLpNorm_restrict_le h p volume _
  -- Kernel-section `Lᵖ'` membership (so the per-point constant is finite).
  have hkermem : ∀ (x' : ℂ) (R : ℝ), 0 < R →
      MemLp (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p'
          volume := by
    intro x' R hR
    -- The membership via the `Lᵖ'` lintegral finiteness.
    have : ENNReal.HolderConjugate p' p := ENNReal.HolderConjugate.symm
    have hp'_top : p' ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr hp1).ne
    have hp'1 : 1 < p' :=
      (ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp (lt_of_le_of_ne le_top hp_top)
    set q' : ℝ := p'.toReal with hq'_def
    have hp'0 : p' ≠ 0 := ne_of_gt (lt_trans one_pos hp'1)
    have hq'1 : 1 < q' := by
      rw [hq'_def, show (1:ℝ) = (1 : ℝ≥0∞).toReal from rfl]
      exact ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp'_top |>.mpr hp'1
    have hq'0 : 0 < q' := lt_trans one_pos hq'1
    have hlint : ∫⁻ u : ℂ in {u : ℂ | R ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q' < ⊤ := by
      rw [← lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
        ← Complex.lintegral_comp_polarCoord_symm]
      set box : ℝ × ℝ → ENNReal := fun p =>
        (Set.Ici R ×ˢ Set.Ioo (-π) π).indicator
          (fun p => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) p with hbox
      have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) := by
        apply ENNReal.measurable_ofReal.comp
        apply Measurable.mul measurable_fst
        exact (Real.continuous_rpow_const hq'0.le).measurable.comp
          ((measurable_fst.pow_const 2).inv)
      have hbound : ∀ pp ∈ polarCoord.target,
          ENNReal.ofReal pp.1 • {u : ℂ | R ≤ ‖u‖}.indicator
            (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (Complex.polarCoord.symm pp) ≤ box pp := by
        intro pp hpp
        rw [polarCoord_target, Set.mem_prod] at hpp
        obtain ⟨hpp1, hpp2⟩ := hpp
        simp only [Set.mem_Ioi] at hpp1
        simp only [hbox]
        have hnorm : ‖Complex.polarCoord.symm pp‖ = pp.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hpp1]
        by_cases hmem : Complex.polarCoord.symm pp ∈ {u : ℂ | R ≤ ‖u‖}
        · have hpR : R ≤ pp.1 := by rw [Set.mem_ofPred_eq, hnorm] at hmem; exact hmem
          rw [Set.indicator_of_mem hmem,
            Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hpR, hpp2⟩)]
          have henorm : ‖Complex.polarCoord.symm pp‖ₑ = ENNReal.ofReal pp.1 := by
            rw [← ofReal_norm, hnorm]
          rw [henorm, smul_eq_mul,
            show ((ENNReal.ofReal pp.1 ^ 2)⁻¹) ^ q' = ENNReal.ofReal (((pp.1^2)⁻¹)^q') by
              rw [← ENNReal.ofReal_pow hpp1.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
                ENNReal.ofReal_rpow_of_pos (by positivity)],
            ← ENNReal.ofReal_mul hpp1.le]
        · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le
      refine lt_of_le_of_lt (setLIntegral_mono
        (hmeas_polar.indicator (measurableSet_Ici.prod measurableSet_Ioo)) hbound) ?_
      calc ∫⁻ pp in polarCoord.target, box pp
          ≤ ∫⁻ pp, box pp := setLIntegral_le_lintegral _ _
        _ = ∫⁻ pp in (Set.Ici R ×ˢ Set.Ioo (-π) π),
              ENNReal.ofReal (pp.1 * ((pp.1^2)⁻¹)^q') := by
              rw [hbox, lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
        _ < ⊤ := by
              rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hmeas_polar.aemeasurable]
              simp only [setLIntegral_const]
              rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
              apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
              have hint2 : IntegrableOn (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q') (Set.Ici R) volume := by
                have heq : (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q')
                    =ᶠ[ae (volume.restrict (Set.Ici R))]
                    (fun ρ : ℝ => ρ^(1 - 2 * q')) := by
                  filter_upwards [ae_restrict_mem measurableSet_Ici] with ρ hρ
                  simp only [Set.mem_Ici] at hρ
                  have hρpos : 0 < ρ := lt_of_lt_of_le hR hρ
                  have hbase : (ρ^2)⁻¹ = ρ^(-2 : ℝ) := by
                    rw [Real.rpow_neg hρpos.le, ← Real.rpow_natCast ρ 2]; norm_num
                  have hh1 : ((ρ^2)⁻¹)^q' = ρ^(-2 * q') := by
                    rw [hbase, ← Real.rpow_mul hρpos.le]
                  have hh2 : ρ * ρ^(-2 * q') = ρ^(1 - 2 * q') := by
                    nth_rewrite 1 [← Real.rpow_one ρ]
                    rw [← Real.rpow_add hρpos]; congr 1; ring
                  rw [hh1, hh2]
                rw [integrableOn_congr_fun_ae heq, integrableOn_Ici_iff_integrableOn_Ioi,
                  integrableOn_Ioi_rpow_iff hR]
                nlinarith [hq'1]
              have hfin := hint2.2
              rw [hasFiniteIntegral_iff_enorm] at hfin
              refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y hy => ?_)) hfin
              · refine (measurable_id.mul ?_).enorm
                exact (Real.continuous_rpow_const hq'0.le).measurable.comp
                  ((measurable_id.pow_const 2).inv)
              · simp only [Set.mem_Ici] at hy
                have hypos : 0 < y := lt_of_lt_of_le hR hy
                rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hmeas : AEStronglyMeasurable
        (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) volume := by
      apply AEStronglyMeasurable.indicator _ measurableSet_ball.compl
      apply Measurable.aestronglyMeasurable
      unfold beurlingKernel; fun_prop
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp'0 hp'_top, ← hq'_def]
    have hpt : ∀ y, ‖(Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y‖ₑ ^ q'
        = (Metric.ball x' R)ᶜ.indicator (fun y => ‖beurlingKernel x' y‖ₑ ^ q') y := by
      intro y
      by_cases h : y ∈ (Metric.ball x' R)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero,
          ENNReal.zero_rpow_of_pos hq'0]
    refine lt_of_eq_of_lt (lintegral_congr hpt) ?_
    rw [lintegral_indicator measurableSet_ball.compl]
    have hkb : ∀ y, ‖beurlingKernel x' y‖ₑ ^ q' ≤ ((‖x' - y‖ₑ ^ 2)⁻¹) ^ q' := by
      intro y
      apply ENNReal.rpow_le_rpow _ hq'0.le
      by_cases h : x' = y
      · subst h; simp [beurlingKernel]
      · have hne : x' - y ≠ 0 := sub_ne_zero.mpr h
        have he : beurlingKernel x' y = ((x'-y) * (x'-y))⁻¹ := by
          rw [beurlingKernel, zpow_neg, zpow_two]
        rw [he, enorm_inv (mul_ne_zero hne hne), enorm_mul, sq]
    refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y _ => hkb y)) ?_
    · exact ENNReal.continuous_rpow_const.measurable.comp
        ((((measurable_const.sub measurable_id).enorm).pow_const 2).inv)
    rw [← lintegral_indicator measurableSet_ball.compl]
    have hsub : (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => ((‖x' - y‖ₑ ^ 2)⁻¹) ^ q') y)
        = (fun y => {u : ℂ | R ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (x' - y)) := by
      funext y
      have hiff : (y ∈ (Metric.ball x' R)ᶜ) ↔ (x' - y ∈ {u : ℂ | R ≤ ‖u‖}) := by
        rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_ofPred_eq, dist_comm,
          Complex.dist_eq]
      by_cases h : y ∈ (Metric.ball x' R)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
    rw [hsub, lintegral_sub_left_eq_self
      (fun u => {u : ℂ | R ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') u) x']
    rw [lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable)]
    exact hlint
  -- Per-point liminf bound (Hölder `Lᵖ`-continuity in the function argument).
  have hLiminfPt : ∀ (R : ℝ), 0 < R → ∀ (x' : ℂ) {f : ℂ → ℂ} {gg : ℕ → ℂ → ℂ},
      MemLp f p volume → (∀ n, MemLp (gg n) p volume) →
      Tendsto (fun n => eLpNorm (f - gg n) p volume) atTop (𝓝 0) →
      ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ liminf (fun n => ‖czOperator beurlingKernel R (gg n) x'‖ₑ) atTop := by
    intro R hR x' f gg hf hgmem htend
    set C := eLpNorm
      (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p' volume with hCdef
    have hbd : ∀ n, ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ ‖czOperator beurlingKernel R (gg n) x'‖ₑ + C * eLpNorm (f - gg n) p volume := by
      intro n
      have hsub : ‖czOperator beurlingKernel R f x' - czOperator beurlingKernel R (gg n) x'‖ₑ
          ≤ C * eLpNorm (f - gg n) p volume := by
        rw [← czOperator_beurling_sub_Lp hp1 hp_top hR x' hf (hgmem n)]
        exact hHolderPt R hR x' (hf.sub (hgmem n))
      calc ‖czOperator beurlingKernel R f x'‖ₑ
          ≤ ‖czOperator beurlingKernel R (gg n) x'‖ₑ
            + ‖czOperator beurlingKernel R f x' - czOperator beurlingKernel R (gg n) x'‖ₑ := by
              rw [add_comm]
              exact le_trans (by rw [sub_add_cancel]) (enorm_add_le _ _)
        _ ≤ _ := by gcongr
    have hCne : C ≠ ⊤ := by rw [hCdef]; exact (hkermem x' R hR).2.ne
    have hC0 : Tendsto (fun n => C * eLpNorm (f - gg n) p volume) atTop (𝓝 0) := by
      simpa using (ENNReal.Tendsto.const_mul htend (Or.inr hCne))
    calc ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ liminf (fun n => ‖czOperator beurlingKernel R (gg n) x'‖ₑ
            + C * eLpNorm (f - gg n) p volume) atTop :=
          le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall hbd)
      _ = liminf (fun n => ‖czOperator beurlingKernel R (gg n) x'‖ₑ) atTop :=
          ENNReal.liminf_add_of_right_tendsto_zero hC0 _
  refine ⟨C₀, fun g hg => ?_⟩
  -- Smooth compactly-supported `Lᵖ`-approximating sequence `gₙ → g`.
  have hp_top' : p ≠ ⊤ := hp_top
  choose gg hggc hggsmooth hggle using fun n : ℕ =>
    hg.exist_eLpNorm_sub_le hp_top' hp1' (ε := 1/(n+1)) (by positivity)
  have hggmem : ∀ n, MemLp (gg n) p volume := fun n =>
    (hggsmooth n).continuous.memLp_of_hasCompactSupport (hggc n)
  have hggBFS : ∀ n, BoundedFiniteSupport (gg n) volume := fun n =>
    boundedFiniteSupport_of_contDiff (hggsmooth n) (hggc n)
  have htend : Tendsto (fun n => eLpNorm (g - gg n) p volume) atTop (𝓝 0) := by
    have hto0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1))) atTop (𝓝 0) := by
      rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
      (fun n => zero_le) hggle
  -- Per-point: `simpleNTO 0 g x ≤ liminf (simpleNTO 0 gₙ x)`.
  have hsup : ∀ x, simpleNontangentialOperator beurlingKernel 0 g x
      ≤ liminf (fun n => simpleNontangentialOperator beurlingKernel 0 (gg n) x) atTop := by
    intro x
    unfold simpleNontangentialOperator
    refine iSup_le (fun R => iSup_le (fun hR => iSup_le (fun x' => iSup_le (fun hx' => ?_))))
    refine le_trans (hLiminfPt R hR x' hg hggmem htend) ?_
    refine liminf_le_liminf (Eventually.of_forall (fun n => ?_))
    exact le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le x' (le_iSup_of_le hx' (le_refl _))))
  -- BFS bound on each `gₙ`.
  have hggbd : ∀ n, eLpNorm (simpleNontangentialOperator beurlingKernel 0 (gg n)) p volume
      ≤ (C₀ : ℝ≥0∞) * eLpNorm (gg n) p volume := fun n => hBFS0 (gg n) (hggBFS n)
  -- `‖gₙ‖_p → ‖g‖_p`.
  have htnorm : Tendsto (fun n => (C₀ : ℝ≥0∞) * eLpNorm (gg n) p volume) atTop
      (𝓝 ((C₀ : ℝ≥0∞) * eLpNorm g p volume)) := by
    have hgnorm : Tendsto (fun n => eLpNorm (gg n) p volume) atTop (𝓝 (eLpNorm g p volume)) := by
      set L := eLpNorm g p volume with hL
      set d := fun n => eLpNorm (g - gg n) p volume with hd
      have hupper : ∀ n, eLpNorm (gg n) p volume ≤ L + d n := by
        intro n
        have h : eLpNorm (gg n) p volume ≤ eLpNorm g p volume + eLpNorm (gg n - g) p volume := by
          calc eLpNorm (gg n) p volume = eLpNorm (g + (gg n - g)) p volume := by
                congr 1; funext y; simp
            _ ≤ eLpNorm g p volume + eLpNorm (gg n - g) p volume :=
                eLpNorm_add_le hg.aestronglyMeasurable ((hggmem n).sub hg).aestronglyMeasurable hp1'
        rw [hL, hd]
        rwa [show eLpNorm (gg n - g) p volume = eLpNorm (g - gg n) p volume from by
          rw [← eLpNorm_neg]; congr 1; funext y; simp] at h
      have hlower : ∀ n, L - d n ≤ eLpNorm (gg n) p volume := by
        intro n
        rw [tsub_le_iff_right]
        calc L = eLpNorm ((gg n) + (g - gg n)) p volume := by rw [hL]; congr 1; funext y; simp
          _ ≤ eLpNorm (gg n) p volume + eLpNorm (g - gg n) p volume :=
              eLpNorm_add_le (hggmem n).aestronglyMeasurable
                (hg.sub (hggmem n)).aestronglyMeasurable hp1'
      have hupper' : Tendsto (fun n => L + d n) atTop (𝓝 L) := by
        simpa using tendsto_const_nhds.add htend
      have hlower' : Tendsto (fun n => L - d n) atTop (𝓝 L) := by
        simpa using (ENNReal.Tendsto.sub (a := L) (b := 0) tendsto_const_nhds htend
          (Or.inr (by simp)))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower' hupper' hlower hupper
    refine ENNReal.Tendsto.const_mul hgnorm ?_
    right; exact ENNReal.coe_ne_top
  -- Fatou on the `Lᵖ` lintegral.
  have hp_pos : (0:ℝ) < p.toReal :=
    ENNReal.toReal_pos (by rintro rfl; exact absurd hp1 (by simp)) hp_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rintro rfl; exact absurd hp1 (by simp)) hp_top]
  simp only [one_div]
  have hmono : ∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 g x‖ₑ ^ p.toReal
      ≤ liminf (fun n => ∫⁻ x,
        ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal) atTop := by
    have hpowliminf : ∀ (u : ℕ → ℝ≥0∞),
        liminf (fun n => (u n) ^ p.toReal) atTop = (liminf u atTop) ^ p.toReal := by
      intro u
      have hmono' : Monotone (fun x : ℝ≥0∞ => x ^ p.toReal) :=
        fun a b h => ENNReal.rpow_le_rpow h hp_pos.le
      exact (hmono'.map_liminf_of_continuousAt u (ENNReal.continuous_rpow_const).continuousAt).symm
    have hle : ∀ x, ‖simpleNontangentialOperator beurlingKernel 0 g x‖ₑ ^ p.toReal
        ≤ liminf (fun n =>
          ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal) atTop := by
      intro x
      simp_rw [enorm_eq_self]
      rw [hpowliminf]
      gcongr
      exact hsup x
    refine le_trans (lintegral_mono hle) ?_
    refine lintegral_liminf_le (fun n => ?_)
    exact (lowerSemicontinuous_simpleNontangentialOperator.measurable).enorm.pow_const _
  calc (∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 g x‖ₑ ^ p.toReal) ^ (p.toReal)⁻¹
      ≤ (liminf (fun n => ∫⁻ x,
          ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal) atTop)
            ^ (p.toReal)⁻¹ := by gcongr
    _ = liminf (fun n => (∫⁻ x,
          ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal)
            ^ (p.toReal)⁻¹) atTop := by
        have hmono2 : Monotone (fun x : ℝ≥0∞ => x ^ (p.toReal)⁻¹) :=
          fun a b h => ENNReal.rpow_le_rpow h (by positivity)
        exact hmono2.map_liminf_of_continuousAt _ (ENNReal.continuous_rpow_const).continuousAt
    _ = liminf (fun n => eLpNorm (simpleNontangentialOperator beurlingKernel 0 (gg n)) p volume)
          atTop := by
        congr 1; funext n
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rintro rfl; exact absurd hp1 (by simp))
          hp_top]
        simp only [one_div]
    _ ≤ liminf (fun n => (C₀ : ℝ≥0∞) * eLpNorm (gg n) p volume) atTop :=
        liminf_le_liminf (Eventually.of_forall hggbd)
    _ = (C₀ : ℝ≥0∞) * eLpNorm g p volume := htnorm.liminf_eq

/-- **A.e. existence of the principal-value limit on `Lᵖ` for `p > 2`** (the
`p < 2` replication with the high maximal bound). -/
lemma czOperator_beurling_ae_tendsto_Lp_high {p : ℝ≥0∞} (hp2 : 2 < p) (hp_top : p ≠ ⊤)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    ∀ᵐ z ∂volume, ∃ L, Filter.Tendsto (fun r => czOperator beurlingKernel r f z)
      (𝓝[>] (0:ℝ)) (𝓝 L) := by
  have hp1 : 1 < p := lt_trans (by norm_num : (1:ℝ≥0∞) < 2) hp2
  have hp1' : (1 : ℝ≥0∞) ≤ p := hp1.le
  have hp_pos : p ≠ 0 := by rintro rfl; exact absurd hp1 (by simp)
  -- Inline helper: oscillation control by the maximal operator (the `Lᵖ` version of
  -- `edist_czOperator_oscillation`, using `czOperator_beurling_sub_Lp`).
  have edist_osc : ∀ {ν : ℂ → ℂ}, MemLp ν p volume → ∀ (z : ℂ) {r₁ r₂ : ℝ}, 0 < r₁ → 0 < r₂ →
      edist (czOperator beurlingKernel r₁ f z) (czOperator beurlingKernel r₂ f z)
        ≤ edist (czOperator beurlingKernel r₁ ν z) (czOperator beurlingKernel r₂ ν z)
          + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
    intro ν hν z r₁ r₂ hr₁ hr₂
    have hd1 : czOperator beurlingKernel r₁ f z - czOperator beurlingKernel r₁ ν z
        = czOperator beurlingKernel r₁ (f - ν) z :=
      (czOperator_beurling_sub_Lp hp1 hp_top hr₁ z hf hν).symm
    have hd2 : czOperator beurlingKernel r₂ f z - czOperator beurlingKernel r₂ ν z
        = czOperator beurlingKernel r₂ (f - ν) z :=
      (czOperator_beurling_sub_Lp hp1 hp_top hr₂ z hf hν).symm
    set Sf1 := czOperator beurlingKernel r₁ f z
    set Sf2 := czOperator beurlingKernel r₂ f z
    set Sn1 := czOperator beurlingKernel r₁ ν z
    set Sn2 := czOperator beurlingKernel r₂ ν z
    have hb1 : edist Sf1 Sn1 ≤ simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
      rw [edist_eq_enorm_sub, hd1]; exact enorm_czOperator_le_simpleNontangential hr₁ (f - ν) z
    have hb2 : edist Sn2 Sf2 ≤ simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
      rw [edist_comm, edist_eq_enorm_sub, hd2]
      exact enorm_czOperator_le_simpleNontangential hr₂ (f - ν) z
    calc edist Sf1 Sf2 ≤ edist Sf1 Sn1 + edist Sn1 Sn2 + edist Sn2 Sf2 := by
          refine le_trans (edist_triangle Sf1 Sn2 Sf2) ?_
          gcongr
          exact edist_triangle Sf1 Sn1 Sn2
      _ = edist Sn1 Sn2 + (edist Sf1 Sn1 + edist Sn2 Sf2) := by ring
      _ ≤ edist Sn1 Sn2 + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
          gcongr; rw [two_mul]; gcongr
  -- Inline helper: per-point Cauchy from smooth convergence + small maximal value
  -- (the `Lᵖ` version of `eventually_edist_lt_of_smooth_conv`).
  have edist_lt_of_conv : ∀ {ν : ℂ → ℂ}, MemLp ν p volume → ∀ (z : ℂ) {a : ℝ≥0∞}, 0 < a →
      (∃ L, Tendsto (fun r => czOperator beurlingKernel r ν z) (𝓝[>] (0:ℝ)) (𝓝 L)) →
      2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z < a / 2 →
      ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z) < a := by
    intro ν hν z a ha hconv hsmall
    obtain ⟨L, hL⟩ := hconv
    have hνcauchy : ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel q.1 ν z) (czOperator beurlingKernel q.2 ν z) < a / 2 := by
      have hmap : Tendsto (fun q : ℝ × ℝ =>
          (czOperator beurlingKernel q.1 ν z, czOperator beurlingKernel q.2 ν z))
          ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) (𝓝 (L, L)) :=
        (hL.comp tendsto_fst).prodMk_nhds (hL.comp tendsto_snd)
      have ht : Tendsto (fun q : ℝ × ℝ =>
          edist (czOperator beurlingKernel q.1 ν z) (czOperator beurlingKernel q.2 ν z))
          ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) (𝓝 (edist L L)) :=
        (continuous_edist.tendsto _).comp hmap
      rw [edist_self] at ht
      exact ht (Iio_mem_nhds (ENNReal.half_pos (ne_of_gt ha)))
    have hpos : ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)), 0 < q.1 ∧ 0 < q.2 := by
      rw [eventually_prod_iff]
      refine ⟨fun r => 0 < r, ?_, fun r => 0 < r, ?_, fun {r₁} h1 {r₂} h2 => ⟨h1, h2⟩⟩
      · exact eventually_mem_of_tendsto_nhdsWithin tendsto_id |>.mono (fun x hx => hx)
      · exact eventually_mem_of_tendsto_nhdsWithin tendsto_id |>.mono (fun x hx => hx)
    filter_upwards [hνcauchy, hpos] with q hq hqpos
    obtain ⟨hq1, hq2⟩ := hqpos
    calc edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z)
        ≤ edist (czOperator beurlingKernel q.1 ν z) (czOperator beurlingKernel q.2 ν z)
          + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z :=
          edist_osc hν z hq1 hq2
      _ < a / 2 + a / 2 := ENNReal.add_lt_add hq hsmall
      _ = a := ENNReal.add_halves a
  -- The smooth `Lᵖ`-dense sequence (inline version of `exists_contDiff_seq_tendsto_L2`).
  choose g hgc hgsmooth hgle using fun n : ℕ =>
    hf.exist_eLpNorm_sub_le hp_top hp1' (ε := 1/(n+1)) (by positivity)
  have hg : ∀ n, MemLp (g n) p volume := fun n =>
    (hgsmooth n).continuous.memLp_of_hasCompactSupport (hgc n)
  have htend : Tendsto (fun n => eLpNorm (f - g n) p volume) atTop (𝓝 0) := by
    have hto0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1))) atTop (𝓝 0) := by
      rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
      (fun n => zero_le) hgle
  -- The maximal-`Lᵖ` Chebyshev bound (inline version of `volume_simpleNontangential_ge_le`).
  obtain ⟨C, hC⟩ := exists_eLpNorm_simpleNontangential_beurling_Lp_high hp2 hp_top
  have vol_ge : ∀ {h : ℂ → ℂ}, MemLp h p volume → ∀ {a : ℝ≥0∞}, a ≠ 0 → a ≠ ⊤ →
      volume {z | a ≤ simpleNontangentialOperator beurlingKernel 0 h z}
        ≤ a⁻¹ ^ p.toReal * ((C : ℝ≥0∞) * eLpNorm h p volume) ^ p.toReal := by
    intro h hh a hane hatop
    have hcheb := meas_ge_le_mul_pow_eLpNorm_enorm volume hp_pos hp_top
      (f := simpleNontangentialOperator beurlingKernel 0 h)
      aestronglyMeasurable_simpleNontangentialOperator (ε := a) hane (fun heq => absurd heq hatop)
    refine le_trans hcheb (mul_le_mul' (le_refl (a⁻¹ ^ p.toReal)) ?_)
    exact ENNReal.rpow_le_rpow (hC h hh) (by positivity)
  -- Inline version of `volume_oscillation_set_eq_zero`.
  have osc_null : ∀ {a : ℝ≥0∞}, 0 < a → a ≠ ⊤ →
      volume {z | ¬ ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z) < a} = 0 := by
    intro a ha ha'
    set b := a / 4 with hbdef
    have hbpos : 0 < b := ENNReal.div_pos (ne_of_gt ha) (by norm_num)
    have hbne : b ≠ 0 := ne_of_gt hbpos
    have hbtop : b ≠ ⊤ := (ENNReal.div_lt_top ha' (by norm_num)).ne
    set B := {z | ¬ ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z) < a}
      with hBdef
    have hsubset : ∀ n, B ⊆ {z | b ≤ simpleNontangentialOperator beurlingKernel 0 (f - g n) z} := by
      intro n z hz
      by_contra hlt
      rw [Set.mem_ofPred_eq, not_le] at hlt
      apply hz
      refine edist_lt_of_conv (hg n) z ha
        ⟨_, czOperator_beurling_tendsto_neg_pi ((hgsmooth n).of_le (by exact_mod_cast le_top))
          (hgc n) z⟩ ?_
      rw [hbdef] at hlt
      calc 2 * simpleNontangentialOperator beurlingKernel 0 (f - g n) z
          < 2 * (a / 4) := by gcongr; exact (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
        _ = a / 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, mul_comm (2:ℝ≥0∞) a, mul_assoc]
            congr 1
            rw [show (4:ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
              ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    have hmeas : ∀ n, volume B
        ≤ b⁻¹ ^ p.toReal * ((C : ℝ≥0∞) * eLpNorm (f - g n) p volume) ^ p.toReal :=
      fun n => le_trans (measure_mono (hsubset n)) (vol_ge (hf.sub (hg n)) hbne hbtop)
    have hto0 : Tendsto
        (fun n => b⁻¹ ^ p.toReal * ((C : ℝ≥0∞) * eLpNorm (f - g n) p volume) ^ p.toReal)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => (C : ℝ≥0∞) * eLpNorm (f - g n) p volume) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul htend (Or.inr ENNReal.coe_ne_top)
      have h2 : Tendsto (fun n => ((C : ℝ≥0∞) * eLpNorm (f - g n) p volume) ^ p.toReal) atTop
          (𝓝 0) := by
        have h := (ENNReal.continuous_rpow_const (y := p.toReal)).continuousAt.tendsto.comp h1
        rw [show ((0:ℝ≥0∞) ^ p.toReal) = 0 by
          rw [ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_pos hp_top)]] at h
        exact h
      have hbinv : b⁻¹ ^ p.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.inv_ne_top.mpr hbne)
      have h3 := ENNReal.Tendsto.const_mul (a := b⁻¹ ^ p.toReal) h2 (Or.inr hbinv)
      rw [mul_zero] at h3
      exact h3
    exact le_antisymm (ge_of_tendsto hto0 (Eventually.of_forall hmeas)) (zero_le)
  -- Assemble: union over the levels `1/(k+1)`, then `tendsto_of_cauchy_edist`.
  set Bk := fun k : ℕ => {z | ¬ ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z)
        < 1/((k:ℝ≥0∞)+1)} with hBk
  have hBknull : ∀ k, volume (Bk k) = 0 := by
    intro k
    apply osc_null
    · apply ENNReal.div_pos one_ne_zero
      exact (ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top k, ENNReal.one_lt_top⟩).ne
    · apply ENNReal.div_ne_top ENNReal.one_ne_top
      have hkp : (0:ℝ≥0∞) < (k:ℝ≥0∞)+1 := by positivity
      exact hkp.ne'
  have hunionnull : volume (⋃ k, Bk k) = 0 := measure_iUnion_null hBknull
  rw [ae_iff]
  refine measure_mono_null ?_ hunionnull
  intro z hz
  rw [Set.mem_ofPred_eq] at hz
  rw [Set.mem_iUnion]
  by_contra hnot
  push Not at hnot
  apply hz
  apply tendsto_of_cauchy_edist
  intro ε hε
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hε)
  have hmem := hnot k
  simp only [hBk, Set.mem_ofPred_eq, not_not] at hmem
  refine hmem.mono (fun q hq => lt_of_lt_of_le hq ?_)
  rw [one_div]
  calc ((k:ℝ≥0∞)+1)⁻¹ ≤ ((k:ℝ≥0∞))⁻¹ := ENNReal.inv_le_inv.mpr le_self_add
    _ ≤ ε := le_of_lt hk

/-- **A.e. convergence of the truncations to `-π · beurling f` on `Lᵖ`, `p > 2`.** -/
lemma czOperator_beurling_ae_tendsto_neg_pi_Lp_high {p : ℝ≥0∞} (hp2 : 2 < p) (hp_top : p ≠ ⊤)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    ∀ᵐ z ∂volume, Filter.Tendsto (fun r => czOperator beurlingKernel r f z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π : ℂ) * beurling f z)) := by
  filter_upwards [czOperator_beurling_ae_tendsto_Lp_high hp2 hp_top hf] with z hz
  obtain ⟨L, hL⟩ := hz
  have hlim : limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r f z) = L := by
    apply Filter.Tendsto.limUnder_eq
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r f z
        = czOperator beurlingKernel r f z := fun r => rfl
    simpa only [hcz] using hL
  have hb : beurling f z = -(1 / (π : ℂ)) * L := by rw [beurling, hlim]
  have hval : -(π:ℂ) * beurling f z = L := by
    rw [hb]; have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [hval]; exact hL

/-- **`Lᵖ` bound for the Beurling transform, `p > 2`, by duality.** The high
truncation bound (`eLpNorm_czOperator_beurling_Lp_high`) passed to the limit by
Fatou using the a.e. convergence `czOperator_beurling_ae_tendsto_neg_pi_Lp_high`.
The constant is `(1/π) · beurlingTruncLpConst p'`. -/
lemma eLpNorm_beurling_Lp_le_high {p : ℝ≥0∞} (hp2 : 2 < p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℂ → ℂ, MemLp f p volume →
      eLpNorm (beurling f) p volume ≤ ENNReal.ofReal C * eLpNorm f p volume := by
  have hp1 : 1 < p := lt_trans (by norm_num : (1:ℝ≥0∞) < 2) hp2
  -- The conjugate exponent `p' = (1 - p⁻¹)⁻¹` and its `HolderConjugate` instance.
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hp'_def
  have hpinv_le_one : p⁻¹ ≤ 1 := by rw [ENNReal.inv_le_one]; exact hp1.le
  have hHC : ENNReal.HolderConjugate p p' := by
    rw [hp'_def, ENNReal.holderConjugate_iff, inv_inv, add_tsub_cancel_of_le hpinv_le_one]
  -- The duality constant.
  set C : ℝ := 1 / π * (beurlingTruncLpConst p' : ℝ) with hCC_def
  refine ⟨C, by positivity, fun f hf => ?_⟩
  have hπpos : (0:ℝ) < 1 / π := by positivity
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- Convert the real constant to the Fatou form `ofReal(1/π) * beurlingTruncLpConst p'`.
  have hCconv : ENNReal.ofReal C
      = ENNReal.ofReal (1 / π) * (beurlingTruncLpConst p' : ℝ≥0∞) := by
    rw [hCC_def, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
  rw [hCconv]
  set Cbound : ℝ≥0∞ :=
    (ENNReal.ofReal (1 / π) * (beurlingTruncLpConst p' : ℝ≥0∞)) * eLpNorm f p volume
    with hCdef
  -- The scaled family `F r = (-(1/π)) • czOperator beurlingKernel r f`.
  set F : ℝ → ℂ → ℂ := fun r => (-(1 / π : ℂ)) • czOperator beurlingKernel r f with hFdef
  -- Bound `eLpNorm (F r) p ≤ Cbound` for `r > 0`.
  have hbound : ∀ᶠ r in 𝓝[>] (0:ℝ), eLpNorm (F r) p volume ≤ Cbound := by
    refine eventually_nhdsWithin_of_forall (fun r hr => ?_)
    rw [Set.mem_Ioi] at hr
    rw [hFdef, eLpNorm_const_smul]
    have hnorm : ‖(-(1 / π : ℂ))‖ₑ = ENNReal.ofReal (1 / π) := by
      rw [← ofReal_norm, norm_neg]
      congr 1
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hnorm, hCdef, mul_assoc]
    exact mul_le_mul' (le_refl _)
      (eLpNorm_czOperator_beurling_Lp_high (p' := p') hp2 hp_top hr hf)
  -- Measurability of each `F r`.
  have hmeas : ∀ r, AEStronglyMeasurable (F r) volume := by
    intro r
    rw [hFdef]
    exact (aestronglyMeasurable_czOperator_beurling' hf.aestronglyMeasurable).const_smul _
  -- a.e. tendsto: scale the a.e. limit by `-(1/π)`.
  have hae : ∀ᵐ z ∂volume, Tendsto (fun r => F r z) (𝓝[>] (0:ℝ)) (𝓝 (beurling f z)) := by
    filter_upwards [czOperator_beurling_ae_tendsto_neg_pi_Lp_high hp2 hp_top hf] with z hz
    have hscaled := hz.const_mul (-(1 / π : ℂ))
    have heq : -(1 / π : ℂ) * (-(π : ℂ) * beurling f z) = beurling f z := by
      field_simp
    rw [heq] at hscaled
    have hFz : (fun r => F r z) = fun r => -(1 / π : ℂ) * czOperator beurlingKernel r f z := by
      funext r; rw [hFdef]; simp [Pi.smul_apply, smul_eq_mul]
    rw [hFz]; exact hscaled
  exact Lp.eLpNorm_le_of_ae_tendsto hbound hmeas hae

/-- **`Lᵖ` boundedness.** For `1 < p < ∞` the Beurling transform is bounded
`Lᵖ(ℂ) → Lᵖ(ℂ)` (Calderón–Zygmund). The range `1 < p < 2` is Marcinkiewicz
interpolation passed to the limit (`eLpNorm_beurling_Lp_le`), `p = 2` is the
`L²` isometry (`beurling_l2_isometry`), and `p > 2` is duality
(`eLpNorm_beurling_Lp_le_high`). -/
theorem beurling_lp_bound (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, IsCalderonZygmundBound beurling p C := by
  rcases lt_trichotomy p 2 with hlt | heq | hgt
  · -- `1 < p < 2`: the truncation bound passed to the limit.
    refine ⟨1 / π * (beurlingTruncLpConst p : ℝ), by positivity, fun f hf => ?_⟩
    have hconv : ENNReal.ofReal (1 / π * (beurlingTruncLpConst p : ℝ))
        = ENNReal.ofReal (1 / π) * (beurlingTruncLpConst p : ℝ≥0∞) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
    rw [hconv]
    exact eLpNorm_beurling_Lp_le hp hlt hf
  · -- `p = 2`: the `L²` isometry.
    subst heq
    exact ⟨1, zero_le_one, fun f hf => by
      rw [beurling_l2_isometry hf, ENNReal.ofReal_one, one_mul]⟩
  · -- `p > 2`: duality.
    obtain ⟨C, hC0, hCb⟩ := eLpNorm_beurling_Lp_le_high hgt hp'
    exact ⟨C, hC0, hCb⟩

/-! ## Operator-norm continuity at `p = 2` (Riesz–Thorin)

The Beurling transform is an `L²` isometry and `Lᵖ`-bounded for every `1 < p < ∞`,
so by Riesz–Thorin complex interpolation (`eLpNorm_interpolation_of_hasStrongType`)
its `Lᵖ` operator norm tends to `1` as `p → 2`. The a.e.-linearity inputs to
interpolation are recorded first. -/

/-- **A.e. convergence of the truncations to `-π · beurling f` on `L² ∪ L⁴`**, a
uniform restatement of the `L²` (`czOperator_beurling_ae_tendsto_neg_pi`) and
`p > 2` (`..._Lp_high`) results — the form consumed by Riesz–Thorin interpolation
(endpoints `p₀ = 2`, `p₁ = 4`). -/
lemma beurling_ae_tendsto_neg_pi_two_four {f : ℂ → ℂ}
    (hf : MemLp f 2 volume ∨ MemLp f 4 volume) :
    ∀ᵐ z ∂volume, Filter.Tendsto (fun r => czOperator beurlingKernel r f z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π : ℂ) * beurling f z)) := by
  rcases hf with hf | hf
  · exact czOperator_beurling_ae_tendsto_neg_pi hf
  · exact czOperator_beurling_ae_tendsto_neg_pi_Lp_high (by norm_num) (by norm_num) hf

/-- Integrability of the truncated Beurling integrand against an `L² ∪ L⁴`
function (`L²` Cauchy–Schwarz, or Hölder with the kernel section in `L^{4/3}`). -/
lemma integrableOn_beurling_two_four {r : ℝ} (hr : 0 < r) (x : ℂ) {f : ℂ → ℂ}
    (hf : MemLp f 2 volume ∨ MemLp f 4 volume) :
    IntegrableOn (fun y => beurlingKernel x y * f y) (Metric.ball x r)ᶜ volume := by
  rcases hf with hf | hf
  · exact integrableOn_beurlingKernel_mul hr x hf
  · have : ENNReal.HolderConjugate (4 : ℝ≥0∞) ((1 - (4 : ℝ≥0∞)⁻¹)⁻¹) :=
      ENNReal.holderConjugate_iff.mpr (by
        rw [inv_inv]; exact add_tsub_cancel_of_le (ENNReal.inv_le_one.mpr (by norm_num)))
    exact integrableOn_beurlingKernel_mul_Lp (p' := (1 - (4 : ℝ≥0∞)⁻¹)⁻¹) hr x
      (by norm_num) (by norm_num) hf

/-- **`beurling` is additive a.e. on `L² ∪ L⁴`** (the truncations are additive and
the a.e. limits add; the limit pins the defining `limUnder` even though `f + g`
need not itself lie in `L² ∪ L⁴`). -/
lemma beurling_add_ae {f g : ℂ → ℂ} (hf : MemLp f 2 volume ∨ MemLp f 4 volume)
    (hg : MemLp g 2 volume ∨ MemLp g 4 volume) :
    beurling (f + g) =ᵐ[volume] beurling f + beurling g := by
  filter_upwards [beurling_ae_tendsto_neg_pi_two_four hf,
    beurling_ae_tendsto_neg_pi_two_four hg] with z hzf hzg
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hconv : Tendsto (fun r => czOperator beurlingKernel r (f + g) z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π:ℂ) * beurling f z + -(π:ℂ) * beurling g z)) := by
    refine (hzf.add hzg).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (czOperator_beurling_add (integrableOn_beurling_two_four hr z hf)
      (integrableOn_beurling_two_four hr z hg)).symm
  have hlim : limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (f + g) z)
      = -(π:ℂ) * beurling f z + -(π:ℂ) * beurling g z := by
    apply Filter.Tendsto.limUnder_eq
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (f + g) z
        = czOperator beurlingKernel r (f + g) z := fun r => rfl
    simpa only [hcz] using hconv
  have hbfg : beurling (f + g) z = -(1 / (π:ℂ)) * limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (f + g) z) := rfl
  have : beurling (f + g) z = beurling f z + beurling g z := by
    rw [hbfg, hlim]; field_simp; ring
  simpa [Pi.add_apply] using this

/-- **`beurling` is homogeneous a.e. on `L² ∪ L⁴`.** -/
lemma beurling_smul_ae (c : ℂ) {f : ℂ → ℂ} (hf : MemLp f 2 volume ∨ MemLp f 4 volume) :
    beurling (c • f) =ᵐ[volume] c • beurling f := by
  filter_upwards [beurling_ae_tendsto_neg_pi_two_four hf] with z hzf
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hconv : Tendsto (fun r => czOperator beurlingKernel r (c • f) z) (𝓝[>] (0:ℝ))
      (𝓝 (c * (-(π:ℂ) * beurling f z))) := by
    refine (hzf.const_mul c).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r _
    exact (czOperator_beurling_const_smul c).symm
  have hlim : limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (c • f) z)
      = c * (-(π:ℂ) * beurling f z) := by
    apply Filter.Tendsto.limUnder_eq
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (c • f) z
        = czOperator beurlingKernel r (c • f) z := fun r => rfl
    simpa only [hcz] using hconv
  have hbcf : beurling (c • f) z = -(1 / (π:ℂ)) * limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r (c • f) z) := rfl
  have : beurling (c • f) z = c * beurling f z := by
    rw [hbcf, hlim]; field_simp
  simpa [Pi.smul_apply, smul_eq_mul] using this

/-- `beurling f` is a.e. strongly measurable for `f ∈ Lᵖ`, `p > 2`. -/
lemma aestronglyMeasurable_beurling_Lp_high {p : ℝ≥0∞} (hp2 : 2 < p) (hp_top : p ≠ ⊤)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    AEStronglyMeasurable (beurling f) volume := by
  set r : ℕ → ℝ := fun n => 1/(n+1:ℝ) with hr
  have hrpos : ∀ n, 0 < r n := fun n => by rw [hr]; positivity
  have hrto : Tendsto r atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨Tendsto.div_atTop tendsto_const_nhds
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop), ?_⟩
    filter_upwards with n; simp only [Set.mem_Ioi, hr]; positivity
  have hae : ∀ᵐ z ∂volume, Tendsto (fun n => czOperator beurlingKernel (r n) f z) atTop
      (𝓝 (-(π:ℂ) * beurling f z)) := by
    filter_upwards [czOperator_beurling_ae_tendsto_neg_pi_Lp_high hp2 hp_top hf] with z hz
    exact hz.comp hrto
  have hmeas : AEStronglyMeasurable (fun z => -(π:ℂ) * beurling f z) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => aestronglyMeasurable_czOperator_beurling' hf.aestronglyMeasurable) hae
  have heq : beurling f = fun z => (-(1/(π:ℂ))) * (-(π:ℂ) * beurling f z) := by
    funext z
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [heq]
  exact hmeas.const_mul _

/-- **Operator-norm continuity at `p = 2`.** The `Lᵖ` bound constant can be taken
arbitrarily close to `1` for `p` near `2` — the qualitative input the Neumann
series of the measurable Riemann mapping theorem consumes. Riesz–Thorin
interpolation between the `L²` isometry (`beurling_l2_isometry`, constant `1`) and
the `L⁴` bound (`beurling_lp_bound`, constant `C₄`) gives `‖T‖_{p→p} ≤ C₄^θ` at
`p = 4/(2-θ) ∈ (2,4)`; choosing `θ` small makes `C₄^θ < 1 + ε`. -/
theorem beurling_opNorm_continuous (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ≥0∞, 2 < p ∧ p ≠ ⊤ ∧ ∃ C : ℝ, C < 1 + ε ∧ IsCalderonZygmundBound beurling p C := by
  -- The `L⁴` bound `‖beurling f‖₄ ≤ ofReal C₄ · ‖f‖₄`.
  obtain ⟨Cq, hCq0, hCqb⟩ := beurling_lp_bound (p := 4) (by norm_num) (by norm_num)
  set M₁ : ℝ≥0 := Cq.toNNReal with hM₁
  have hM₁coe : (M₁ : ℝ) = Cq := Real.coe_toNNReal Cq hCq0
  -- Choose `θ ∈ (0,1)` with `Cq ^ θ < 1 + ε`.
  obtain ⟨θ, hθ0, hθ1, hθlt⟩ : ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ Cq ^ θ < 1 + ε := by
    by_cases hCq1 : Cq ≤ 1
    · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      calc Cq ^ (1 / 2 : ℝ) ≤ (1 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hCq0 hCq1 (by norm_num)
        _ = 1 := Real.one_rpow _
        _ < 1 + ε := by linarith
    · push Not at hCq1
      have hlogpos : 0 < Real.log Cq := Real.log_pos hCq1
      have hlog1ε : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
      refine ⟨min (1 / 2) (Real.log (1 + ε) / (2 * Real.log Cq)),
        lt_min (by norm_num) (by positivity),
        lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_⟩
      rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < Cq)]
      calc Real.exp (Real.log Cq * min (1 / 2) (Real.log (1 + ε) / (2 * Real.log Cq)))
          < Real.exp (Real.log (1 + ε)) := by
            apply Real.exp_lt_exp.mpr
            calc Real.log Cq * min (1 / 2) (Real.log (1 + ε) / (2 * Real.log Cq))
                ≤ Real.log Cq * (Real.log (1 + ε) / (2 * Real.log Cq)) :=
                  mul_le_mul_of_nonneg_left (min_le_right _ _) hlogpos.le
              _ = Real.log (1 + ε) / 2 := by field_simp
              _ < Real.log (1 + ε) := by linarith
        _ = 1 + ε := Real.exp_log (by linarith)
  -- The intermediate exponent `p = 4/(2-θ) ∈ (2,4)`.
  have h2θpos : (0 : ℝ) < 2 - θ := by linarith
  have hppos : (0 : ℝ) < 4 / (2 - θ) := by positivity
  set p : ℝ≥0∞ := ENNReal.ofReal (4 / (2 - θ)) with hpdef
  have hp2 : (2 : ℝ≥0∞) < p := by
    rw [hpdef, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ENNReal.ofReal_lt_ofReal_iff hppos, lt_div_iff₀ h2θpos]; linarith
  have hptop : p ≠ ⊤ := by rw [hpdef]; exact ENNReal.ofReal_ne_top
  -- The interpolation exponent relation `1/p = (1-θ)/2 + θ/4`.
  have hprel : p⁻¹ = ENNReal.ofReal (1 - θ) * (2 : ℝ≥0∞)⁻¹ + ENNReal.ofReal θ * (4 : ℝ≥0∞)⁻¹ := by
    have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
        show ENNReal.ofReal 2 = 2 by simp, one_div]
    have h4 : (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 4) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
        show ENNReal.ofReal 4 = 4 by simp, one_div]
    rw [hpdef, ← ENNReal.ofReal_inv_of_pos hppos, h2, h4,
      ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 - θ),
      ← ENNReal.ofReal_mul hθ0.le,
      ← ENNReal.ofReal_add (mul_nonneg (by linarith) (by norm_num))
        (mul_nonneg hθ0.le (by norm_num))]
    congr 1
    field_simp
    ring
  refine ⟨p, hp2, hptop, Cq ^ θ, hθlt, by positivity, fun f hf => ?_⟩
  -- Apply Riesz–Thorin (`p₀ = 2`, `M₀ = 1`; `p₁ = 4`, `M₁ = C₄`).
  have hinterp := eLpNorm_interpolation_of_hasStrongType
    (T := beurling) (p₀ := 2) (p₁ := 4) (M₀ := 1) (M₁ := M₁) (θ := θ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨hθ0, hθ1⟩ hprel
    (fun s hs => aestronglyMeasurable_beurling_Lp_high hp2 hptop hs)
    (fun s t hs ht => beurling_add_ae hs ht)
    (fun c s hs => beurling_smul_ae c hs)
    (fun s hs => by rw [beurling_l2_isometry hs]; simp)
    (fun s hs => hCqb s hs)
    hf
  refine le_trans hinterp (le_of_eq ?_)
  congr 1
  rw [NNReal.one_rpow, one_mul, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_rpow, hM₁coe]

end NoWanderingDomains
