/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.MRMT.NeumannSeries.CauchyTransform

/-!
# The Neumann-series principal solution of the Beltrami equation

For a Beltrami coefficient `b` (measurable `μ` with `‖μ‖∞ < 1`) vanishing outside a ball, the
**principal solution** of `∂̄f = μ·∂f` is `f = id + P h`, where `P` is the Cauchy transform and
`h ∈ Lᵖ(ℂ)` solves `h = μ·S h + μ` almost everywhere, for an exponent `2 < p < ∞` with
`‖μ‖∞·C < 1`, `C` a Calderón–Zygmund bound for the Beurling transform `S` at `p`. The companion
file `NeumannSeries/CauchyTransform.lean` supplies the analytic input on `P`: for a compactly
vanishing `Lᵖ` field with `p > 2` the defining integral converges, `P h` is globally Hölder
continuous with exponent `1 − 2/p`, and `P h z → 0` cocompactly. This file adds the weak
derivative identities for `P h`, the Banach fixed point producing `h`, and the bundle
`IsPrincipalSolution` with its existence, uniqueness and property API; the homeomorphism and
orientation upgrades live in `QC/MRMT/Existence.lean`.

## Main definitions

* `NoWanderingDomains.IsPrincipalSolution` — `IsPrincipalSolution b f` records the Neumann-series
  data: some `2 < p`, `p ≠ ⊤`, radius `R` and `h ∈ Lᵖ(ℂ)` with `h z = 0` whenever `R < ‖z‖` and
  `h =ᵐ[volume] fun z => b.μ z * S h z + b.μ z`, together with `f z = z + P h z` for every `z`.

## Main results

* `NoWanderingDomains.hasWeakGradient_cauchyTransform` — for `2 < p`, `p ≠ ⊤`, `MemLp h p volume`
  and `∀ z, R < ‖z‖ → h z = 0`, the transform `P h` has weak partials `S h + h` (direction `1`)
  and `i·(S h − h)` (direction `i`) on all of `ℂ`. In the Wirtinger dictionary
  `∂ = ½(gx − i·gy)`, `∂̄ = ½(gx + i·gy)` this reads `∂̄(P h) = h` and `∂(P h) = S h`.
* `NoWanderingDomains.exists_lp_fixedPoint_beltrami` — for `2 < p`, `p ≠ ⊤`, measurable `μ` with
  `eLpNormEssSup μ volume ≠ ⊤`, a bound `IsCalderonZygmundBound beurling p C` and the
  contraction hypothesis `‖μ‖∞·C < 1`, every datum `g ∈ Lᵖ` yields `h ∈ Lᵖ` with
  `h =ᵐ μ·S h + g` and `‖h‖ₚ ≤ (1 − ‖μ‖∞·C)⁻¹·‖g‖ₚ`. The datum is kept general: `g = μ` gives
  the principal-solution field, and the auxiliary equations elsewhere reuse the same solve.
* `NoWanderingDomains.exists_isPrincipalSolution` — a Beltrami coefficient vanishing outside a ball
  (`∀ z, R < ‖z‖ → b.μ z = 0`) admits a principal solution; the exponent comes from
  `exists_p_gt_two_beurling_contraction` and the field from the fixed point with datum `g = b.μ`.
* `NoWanderingDomains.IsPrincipalSolution.continuous` — a principal solution is continuous on `ℂ`.
* `NoWanderingDomains.IsPrincipalSolution.tendsto_sub_id_cocompact` — the principal normalization:
  `f z − z → 0` along `cocompact ℂ`.
* `NoWanderingDomains.IsPrincipalSolution.hasWeakGradient` — a principal solution has weak partials
  `1 + (S h + h)` and `i·(1 + (S h − h))` on all of `ℂ`, both locally `L²`, for some `h ∈ Lᵖ`
  (`2 < p`, `p ≠ ⊤`) with `h =ᵐ b.μ·S h + b.μ`; the identity contributes `1` and `i`.
* `NoWanderingDomains.IsPrincipalSolution.memW12loc` — a principal solution is `W^{1,2}_loc` on `ℂ`.
* `NoWanderingDomains.IsPrincipalSolution.weak_beltrami` — a principal solution has a weak gradient
  `u`, `v` on all of `ℂ`, locally `L²` and a.e. strongly measurable, with
  `½(u + i·v) = b.μ · ½(u − i·v)` almost everywhere — the equation `∂̄f = μ·∂f` in weak form.
* `NoWanderingDomains.isPrincipalSolution_unique` — two principal solutions of the same coefficient
  are equal as functions, whatever exponents and radii produced them: the difference `δ` of the
  fixed-point fields is `L²` and solves `δ =ᵐ μ·S δ`, so the `L²` isometry of `S` together with
  `‖μ‖∞ < 1` forces `δ = 0`, and the Cauchy transforms agree.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **Weak derivative identities for the Cauchy transform of a compactly vanishing
`Lᵖ` field** (`p > 2`): `∂̄(P h) = h` and `∂(P h) = S h` in the weak (distributional)
sense, packaged on the coordinate partials as

`HasWeakGradient (S h + h) (i·(S h − h)) (P h) univ`

(the Wirtinger dictionary `gx = ∂ + ∂̄`, `gy = i(∂ − ∂̄)`). Proof: mollify `h` by
convolution inside a slightly larger ball, apply the smooth identities
`dzbar_cauchyTransform` and `beurling_eq_dz_cauchyTransform`, and pass the
integration-by-parts identities to the limit — the mollifications converge in `Lᵖ`,
hence the transforms converge uniformly (Hölder bound) and `S`-images converge in
`Lᵖ` (Calderón–Zygmund bound). -/
theorem hasWeakGradient_cauchyTransform {h : ℂ → ℂ} {p : ℝ≥0∞} {R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤) (hh : MemLp h p volume)
    (hsupp : ∀ z : ℂ, R < ‖z‖ → h z = 0) :
    HasWeakGradient (fun z => beurling h z + h z)
      (fun z => Complex.I * (beurling h z - h z)) (cauchyTransform h) Set.univ := by
  have hCT1 : ∀ {u : ℂ → ℂ} {R' : ℝ}, MemLp u p volume →
      (∀ z : ℂ, R' < ‖z‖ → u z = 0) →
      ∀ z : ℂ, Integrable (fun ζ => u ζ / (ζ - z)) volume :=
    fun {u R'} hu hus z => integrable_div_sub_of_memLp_of_support hp hp' hu hus z
  have hCT3 : ∀ {u : ℂ → ℂ} {R' : ℝ}, MemLp u p volume →
      (∀ z : ℂ, R' < ‖z‖ → u z = 0) →
      Continuous (cauchyTransform u) :=
    fun {u R'} hu hus => continuous_cauchyTransform_of_memLp_of_support hp hp' hu hus
  -- ===== PART 0: exponents =====
  set pr : ℝ := p.toReal with hpr_def
  have hp0 : p ≠ 0 := (lt_trans (by norm_num : (0:ℝ≥0∞) < 2) hp).ne'
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_of_lt (lt_trans ENNReal.one_lt_two hp)
  have hp2 : (2 : ℝ≥0∞) ≤ p := hp.le
  have hpr2 : 2 < pr := by
    have h2 := (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hp').mpr hp
    simpa [← hpr_def] using h2
  have hpr0 : 0 < pr := lt_trans two_pos hpr2
  set qr : ℝ := (1 - pr⁻¹)⁻¹ with hqr_def
  have hainv0 : 0 < pr⁻¹ := inv_pos.mpr hpr0
  have hainv : pr⁻¹ < 2⁻¹ := by
    have hmul : pr * pr⁻¹ = 1 := mul_inv_cancel₀ hpr0.ne'
    nlinarith [hainv0, hpr2, hmul]
  have hb0 : 0 < 1 - pr⁻¹ := by
    have h12 : (2 : ℝ)⁻¹ < 1 := by norm_num
    linarith
  have hbinv0 : 0 < (1 - pr⁻¹)⁻¹ := inv_pos.mpr hb0
  have hbmul : (1 - pr⁻¹) * (1 - pr⁻¹)⁻¹ = 1 := mul_inv_cancel₀ hb0.ne'
  have hqr1 : 1 < qr := by
    rw [hqr_def]
    nlinarith [hbmul, mul_pos hainv0 hbinv0, hbinv0]
  have hqr2 : qr < 2 := by
    rw [hqr_def]
    nlinarith [hbmul, hainv, hbinv0]
  have hqr0 : 0 < qr := lt_trans one_pos hqr1
  have hpq : pr.HolderConjugate qr := by
    refine ⟨?_, hpr0, hqr0⟩
    rw [hqr_def, inv_inv, inv_one]
    ring
  have hpq2 : ENNReal.HolderConjugate 2 2 := by
    rw [ENNReal.holderConjugate_iff]
    simp [ENNReal.inv_two_add_inv_two]
  have hpq22 : (2:ℝ).HolderConjugate 2 := ⟨by norm_num, two_pos, two_pos⟩
  -- ===== PART 1: radial kernel machinery (CT2 pattern) =====
  have hpt : ∀ w : ℂ, ‖w⁻¹‖ₑ ^ qr = ENNReal.ofReal (‖w‖ ^ (-qr)) := fun w => by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hqr0.le,
      norm_inv, Real.inv_rpow (norm_nonneg w), ← Real.rpow_neg (norm_nonneg w)]
  have hnegpow_int : ∀ r : ℝ, 0 < r →
      IntegrableOn (fun w : ℂ => ‖w‖ ^ (-qr)) (Metric.ball (0:ℂ) r) volume := by
    intro r hr
    rw [← integrable_indicator_iff measurableSet_ball]
    set F : ℝ → ℝ := fun t : ℝ => if t < r then t ^ (-qr) else 0 with hF
    have heq : (Metric.ball (0:ℂ) r).indicator (fun w : ℂ => ‖w‖ ^ (-qr))
        = fun w : ℂ => F ‖w‖ := by
      funext w
      simp only [Set.indicator, hF]
      by_cases hw : w ∈ Metric.ball (0:ℂ) r
      · rw [if_pos hw]
        have hwr : ‖w‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        rw [if_pos hwr]
      · rw [if_neg hw]
        have hwr : ¬ ‖w‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        rw [if_neg hwr]
    rw [heq]
    rw [show (fun w : ℂ => F ‖w‖) = (F ‖·‖) from rfl]
    rw [integrable_fun_norm_addHaar volume]
    rw [Complex.finrank_real_complex]
    have hbase : IntegrableOn
        ((Set.Ioo (0 : ℝ) r).indicator fun y : ℝ => y ^ (1 - qr)) (Set.Ioi 0) volume := by
      rw [integrableOn_indicator_iff measurableSet_Ioo]
      have hsub : Set.Ioo (0 : ℝ) r ∩ Set.Ioi 0 = Set.Ioo (0 : ℝ) r :=
        Set.inter_eq_left.mpr fun y hy => hy.1
      rw [hsub, intervalIntegral.integrableOn_Ioo_rpow_iff hr]
      linarith
    apply hbase.congr_fun _ measurableSet_Ioi
    intro y hy
    simp only [Set.mem_Ioi] at hy
    simp only [hF, smul_eq_mul, Set.indicator]
    by_cases hyR : y < r
    · rw [if_pos ⟨hy, hyR⟩, if_pos hyR,
        show (1 - qr) = (1 : ℝ) + (-qr) by ring, Real.rpow_add hy, Real.rpow_one]
      norm_num
    · rw [if_neg fun hc => hyR hc.2, if_neg hyR, mul_zero]
  have hball_val : ∀ r : ℝ, 0 < r →
      ∫ w in Metric.ball (0:ℂ) r, ‖w‖ ^ (-qr) ≤ 2 * Real.pi / (2 - qr) * r ^ (2 - qr) := by
    intro r hr
    set f : ℝ → ℝ := fun t => if t < r then t ^ (-qr) else 0 with hf
    have hconv : ∫ w in Metric.ball (0:ℂ) r, ‖w‖ ^ (-qr) = ∫ x : ℂ, f ‖x‖ := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ Metric.ball (0:ℂ) r
      · rw [Set.indicator_of_mem hx]
        simp only [hf]
        rw [Metric.mem_ball, dist_zero_right] at hx
        rw [if_pos hx]
      · rw [Set.indicator_of_notMem hx]
        simp only [hf]
        rw [Metric.mem_ball, dist_zero_right] at hx
        rw [if_neg hx]
    rw [hconv]
    rw [integral_fun_norm_addHaar volume f, Complex.finrank_real_complex]
    have hvol : volume.real (Metric.ball (0:ℂ) 1) = Real.pi := by
      rw [Measure.real, Complex.volume_ball]; simp
    rw [hvol]
    have hinner : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • f y = r ^ (2 - qr) / (2 - qr) := by
      have hsub' : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • f y
          = ∫ y in Set.Ioo (0:ℝ) r, y ^ (2 - 1) • f y := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        · intro x hx
          simp only [Set.mem_Ioo, Set.mem_Ioi] at *
          exact hx.1
        · intro x hx
          simp only [Set.mem_Ioi, Set.mem_Ioo, Set.mem_sdiff, not_and, not_lt] at hx
          obtain ⟨hx0, hxR⟩ := hx
          have hnlt : ¬ (x < r) := not_lt.mpr (hxR hx0)
          rw [hf]; simp only [if_neg hnlt, smul_zero]
      rw [hsub']
      have hcongr : ∫ y in Set.Ioo (0:ℝ) r, y ^ (2 - 1) • f y
          = ∫ y in Set.Ioo (0:ℝ) r, y ^ (1 - qr) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro y hy
        simp only [Set.mem_Ioo] at hy
        rw [hf]
        simp only [if_pos hy.2]
        rw [pow_one, smul_eq_mul]
        rw [show y * y ^ (-qr) = y ^ (1:ℝ) * y ^ (-qr) by rw [Real.rpow_one]]
        rw [← Real.rpow_add hy.1]
        ring_nf
      rw [hcongr]
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
      rw [integral_rpow (Or.inl (by linarith))]
      have h1 : (1 : ℝ) - qr + 1 = 2 - qr := by ring
      rw [h1, Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < 2 - qr))]
      ring
    rw [hinner]
    rw [le_iff_lt_or_eq]; right
    rw [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
  have htransl : ∀ S₀ : Set ℂ, MeasurableSet S₀ → ∀ (g : ℂ → ℝ≥0∞) (y : ℂ),
      ∫⁻ ζ in {ζ : ℂ | ζ - y ∈ S₀}, g (ζ - y) = ∫⁻ w in S₀, g w := by
    intro S₀ hS₀ g y
    have hpre : MeasurableSet {ζ : ℂ | ζ - y ∈ S₀} := (measurable_id.sub_const y) hS₀
    calc ∫⁻ ζ in {ζ : ℂ | ζ - y ∈ S₀}, g (ζ - y)
        = ∫⁻ ζ, ({ζ : ℂ | ζ - y ∈ S₀}).indicator (fun ζ => g (ζ - y)) ζ := by
          rw [lintegral_indicator hpre]
      _ = ∫⁻ ζ, S₀.indicator g (ζ - y) := by
          apply lintegral_congr
          intro ζ
          unfold Set.indicator
          by_cases hζ : ζ - y ∈ S₀
          · rw [if_pos hζ, if_pos (by exact hζ)]
          · rw [if_neg hζ, if_neg (by exact hζ)]
      _ = ∫⁻ ζ, S₀.indicator g ζ := lintegral_sub_right_eq_self _ y
      _ = ∫⁻ w in S₀, g w := by rw [lintegral_indicator hS₀]
  have hballE : ∀ (y : ℂ) (r : ℝ), 0 < r →
      ∫⁻ ζ in Metric.ball y r, ‖(ζ - y)⁻¹‖ₑ ^ qr
        ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * r ^ (2 - qr)) := by
    intro y r hr
    have hset : Metric.ball y r = {ζ : ℂ | ζ - y ∈ Metric.ball (0:ℂ) r} := by
      ext ζ
      simp [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc ∫⁻ ζ in Metric.ball y r, ‖(ζ - y)⁻¹‖ₑ ^ qr
        = ∫⁻ w in Metric.ball (0:ℂ) r, ‖w⁻¹‖ₑ ^ qr := by
          rw [hset]
          exact htransl _ measurableSet_ball (fun w => ‖w⁻¹‖ₑ ^ qr) y
      _ = ∫⁻ w in Metric.ball (0:ℂ) r, ENNReal.ofReal (‖w‖ ^ (-qr)) := lintegral_congr hpt
      _ = ENNReal.ofReal (∫ w in Metric.ball (0:ℂ) r, ‖w‖ ^ (-qr)) :=
          (ofReal_integral_eq_lintegral_ofReal (hnegpow_int r hr)
            (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (norm_nonneg w) _)).symm
      _ ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * r ^ (2 - qr)) :=
          ENNReal.ofReal_le_ofReal (hball_val r hr)
  have hconst : ‖-(1/(Real.pi:ℂ))‖ = 1/Real.pi := by
    rw [norm_neg, norm_div, norm_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  -- ===== PART 2: geometry and L² facts =====
  set m : ℝ := max R 0 with hm_def
  have hm0 : 0 ≤ m := le_max_right R 0
  set ρ : ℝ := m + 2 with hρ_def
  have hρ0 : 0 < ρ := by rw [hρ_def]; linarith
  have hRρ : R ≤ ρ := by
    rw [hρ_def]
    have := le_max_left R 0
    rw [← hm_def] at this
    linarith
  have hsuppρ : ∀ ζ : ℂ, ρ < ‖ζ‖ → h ζ = 0 := fun ζ hζ =>
    hsupp ζ (lt_of_le_of_lt hRρ hζ)
  set B : Set ℂ := Metric.closedBall (0:ℂ) ρ with hB_def
  have hBmeas : MeasurableSet B := by rw [hB_def]; exact measurableSet_closedBall
  have hBfin : volume B < ⊤ := by
    rw [hB_def]
    exact (isCompact_closedBall _ _).measure_lt_top
  have : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBfin⟩
  -- L² membership of `h`
  have hL2h : MemLp h 2 volume := by
    have hind : h = B.indicator h := by
      funext ζ
      by_cases hζ : ζ ∈ B
      · rw [Set.indicator_of_mem hζ]
      · rw [Set.indicator_of_notMem hζ]
        refine hsuppρ ζ ?_
        simpa [hB_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
    rw [hind]
    exact (memLp_indicator_iff_restrict hBmeas).2 ((hh.restrict B).mono_exponent hp2)
  -- the L² ↪ Lᵖ embedding constant on `B`
  set cB : ℝ≥0∞ := volume B ^ (1/(2:ℝ) - 1/pr) with hcB_def
  have hcB_ne : cB ≠ ⊤ := by
    rw [hcB_def]
    refine (ENNReal.rpow_lt_top_of_nonneg ?_ hBfin.ne).ne
    have h2pr : 1/pr ≤ 1/2 := by
      apply one_div_le_one_div_of_le two_pos hpr2.le
    linarith
  have hemb : ∀ w : ℂ → ℂ, MemLp w p volume → (∀ ζ : ℂ, ρ < ‖ζ‖ → w ζ = 0) →
      eLpNorm w 2 volume ≤ eLpNorm w p volume * cB := by
    intro w hw hwsupp
    have hwind : w = B.indicator w := by
      funext ζ
      by_cases hζ : ζ ∈ B
      · rw [Set.indicator_of_mem hζ]
      · rw [Set.indicator_of_notMem hζ]
        refine hwsupp ζ ?_
        simpa [hB_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
    calc eLpNorm w 2 volume = eLpNorm w 2 (volume.restrict B) := by
          conv_lhs => rw [hwind]
          exact eLpNorm_indicator_eq_eLpNorm_restrict hBmeas
      _ ≤ eLpNorm w p (volume.restrict B)
            * (volume.restrict B) Set.univ ^ (1/(2:ℝ≥0∞).toReal - 1/p.toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp2 hw.1.restrict
      _ = eLpNorm w p (volume.restrict B) * cB := by
          rw [Measure.restrict_apply_univ, hcB_def, hpr_def]
          norm_num
      _ ≤ eLpNorm w p volume * cB :=
          mul_le_mul' (eLpNorm_mono_measure _ Measure.restrict_le_self) le_rfl
  -- ===== PART 3: the L² pairing bound =====
  have hpair : ∀ (u ψ : ℂ → ℂ), MemLp u 2 volume → MemLp ψ 2 volume →
      ‖∫ z, u z * ψ z‖ ≤ (eLpNorm u 2 volume).toReal * (eLpNorm ψ 2 volume).toReal := by
    intro u ψ hu hψ
    have henorm : ‖∫ z, u z * ψ z‖ₑ ≤ eLpNorm u 2 volume * eLpNorm ψ 2 volume := by
      calc ‖∫ z, u z * ψ z‖ₑ
          ≤ ∫⁻ z, ‖u z * ψ z‖ₑ := enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ z, ‖u z‖ₑ * ‖ψ z‖ₑ := lintegral_congr fun z => enorm_mul _ _
        _ ≤ (∫⁻ z, ‖u z‖ₑ ^ (2:ℝ)) ^ (1/(2:ℝ)) * (∫⁻ z, ‖ψ z‖ₑ ^ (2:ℝ)) ^ (1/(2:ℝ)) :=
            ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq22 hu.1.enorm hψ.1.enorm
        _ = eLpNorm u 2 volume * eLpNorm ψ 2 volume := by
            rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
              eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
            norm_num
    have hfin : eLpNorm u 2 volume * eLpNorm ψ 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top hu.2.ne hψ.2.ne
    calc ‖∫ z, u z * ψ z‖
        = (‖∫ z, u z * ψ z‖ₑ).toReal := by
          rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
      _ ≤ (eLpNorm u 2 volume * eLpNorm ψ 2 volume).toReal := ENNReal.toReal_mono hfin henorm
      _ = _ := ENNReal.toReal_mul
  have hintpair : ∀ (u ψ : ℂ → ℂ), MemLp u 2 volume → MemLp ψ 2 volume →
      Integrable (fun z => u z * ψ z) volume := fun u ψ hu hψ => hu.integrable_mul hψ
  -- ===== PART 4: the smooth approximating sequence =====
  set χb : ContDiffBump (0:ℂ) := ⟨m+1, m+2, by linarith, by linarith⟩ with hχb_def
  have hrOut : χb.rOut = ρ := by rw [hχb_def, hρ_def]
  have hrIn : χb.rIn = m+1 := by rw [hχb_def]
  have hχsupp : ∀ z : ℂ, ρ < ‖z‖ → χb z = 0 := by
    intro z hz
    apply Function.notMem_support.mp
    rw [χb.support_eq, hrOut]
    simp only [Metric.mem_ball, dist_zero_right, not_lt]
    exact hz.le
  have hχ1 : ∀ z : ℂ, ‖z‖ ≤ m+1 → χb z = 1 := by
    intro z hz
    apply χb.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, hrIn]
    exact hz
  have hchoice : ∀ n : ℕ, ∃ u : ℂ → ℂ, HasCompactSupport u ∧ ContDiff ℝ (⊤:ℕ∞) u ∧
      eLpNorm (h - u) p volume ≤ ENNReal.ofReal (1/(n+1)) := by
    intro n
    exact hh.exist_eLpNorm_sub_le hp' hp1 (by positivity)
  choose useq hucs husm huclose using hchoice
  set hseq : ℕ → ℂ → ℂ := fun n z => χb z • useq n z with hhseq_def
  have hseqsm : ∀ n, ContDiff ℝ (⊤:ℕ∞) (hseq n) := fun n => χb.contDiff.smul (husm n)
  have hseqcs : ∀ n, HasCompactSupport (hseq n) := fun n =>
    χb.hasCompactSupport.smul_right
  have hseqsupp : ∀ n, ∀ z : ℂ, ρ < ‖z‖ → hseq n z = 0 := by
    intro n z hz
    simp only [hhseq_def]
    rw [hχsupp z hz]
    exact zero_smul ℝ _
  have hseqLp : ∀ n, MemLp (hseq n) p volume := fun n =>
    ((hseqsm n).continuous).memLp_of_hasCompactSupport (hseqcs n)
  have hseqL2 : ∀ n, MemLp (hseq n) 2 volume := fun n =>
    ((hseqsm n).continuous).memLp_of_hasCompactSupport (hseqcs n)
  have hseqclose : ∀ n, eLpNorm (fun z => h z - hseq n z) p volume
      ≤ ENNReal.ofReal (1/(n+1)) := by
    intro n
    have hptw : ∀ z : ℂ, ‖h z - hseq n z‖ ≤ ‖(h - useq n) z‖ := by
      intro z
      simp only [hhseq_def, Pi.sub_apply]
      by_cases hz : ‖z‖ ≤ m+1
      · rw [hχ1 z hz, Complex.real_smul]
        simp
      · have hz' : R < ‖z‖ := by
          have hm1 : m < ‖z‖ := by
            have := not_le.mp hz
            linarith
          exact lt_of_le_of_lt (le_max_left R 0) hm1
        rw [hsupp z hz']
        rw [zero_sub, zero_sub, norm_neg, norm_neg, Complex.real_smul, norm_mul,
          Complex.norm_real]
        apply mul_le_of_le_one_left (norm_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg χb.nonneg]
        exact χb.le_one
    exact le_trans (eLpNorm_mono hptw) (huclose n)
  have hδp : Tendsto (fun n : ℕ => (eLpNorm (fun z => h z - hseq n z) p volume).toReal)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    calc (eLpNorm (fun z => h z - hseq n z) p volume).toReal
        ≤ (ENNReal.ofReal (1/(n+1))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hseqclose n)
      _ = 1/(n+1) := ENNReal.toReal_ofReal (by positivity)
  have hδ2 : Tendsto (fun n : ℕ => (eLpNorm (fun z => hseq n z - h z) 2 volume).toReal)
      atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ, (eLpNorm (fun z => hseq n z - h z) 2 volume).toReal
        ≤ (eLpNorm (fun z => h z - hseq n z) p volume).toReal * cB.toReal := by
      intro n
      have hwsupp : ∀ ζ : ℂ, ρ < ‖ζ‖ → h ζ - hseq n ζ = 0 := by
        intro ζ hζ
        rw [hsuppρ ζ hζ, hseqsupp n ζ hζ, sub_zero]
      have h1 := hemb (fun ζ => h ζ - hseq n ζ) (hh.sub (hseqLp n)) hwsupp
      have hflip : eLpNorm (fun z => hseq n z - h z) 2 volume
          = eLpNorm (fun z => h z - hseq n z) 2 volume := eLpNorm_sub_comm _ _ _ _
      rw [hflip]
      calc (eLpNorm (fun z => h z - hseq n z) 2 volume).toReal
          ≤ (eLpNorm (fun z => h z - hseq n z) p volume * cB).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top (hh.sub (hseqLp n)).2.ne hcB_ne) h1
        _ = _ := ENNReal.toReal_mul
    have hmul := hδp.mul_const cB.toReal
    rw [zero_mul] at hmul
    exact squeeze_zero (fun n => ENNReal.toReal_nonneg) hbound hmul
  -- ===== PART 5: the smooth case =====
  have hsmoothgrad : ∀ u : ℂ → ℂ, ContDiff ℝ (⊤:ℕ∞) u → HasCompactSupport u →
      HasWeakDirDeriv 1 (fun z => beurling u z + u z) (cauchyTransform u) Set.univ ∧
      HasWeakDirDeriv Complex.I (fun z => Complex.I * (beurling u z - u z))
        (cauchyTransform u) Set.univ := by
    intro u hu hucs
    have hu1 : ContDiff ℝ 1 u := hu.of_le (by exact_mod_cast le_top)
    have hF : ContDiff ℝ (⊤ : ℕ∞) (cauchyTransform u) := by
      set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ with hL
      set k : ℂ → ℂ := fun w => -w⁻¹ with hk
      have hk_loc : LocallyIntegrable k volume := by
        rw [hk]
        apply LocallyIntegrable.neg
        rw [MeasureTheory.locallyIntegrable_iff]
        intro K hK
        obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
        apply MeasureTheory.IntegrableOn.mono_set _ hR₀
        rw [IntegrableOn]
        refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
        rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
          ← Complex.lintegral_comp_polarCoord_symm]
        set box : ℝ × ℝ → ENNReal :=
          (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
            (fun _ => (1 : ENNReal)) with hbox
        have hbound : ∀ q ∈ polarCoord.target,
            ENNReal.ofReal q.1 • (Metric.closedBall (0 : ℂ) R₀).indicator
              (fun w : ℂ => ‖w⁻¹‖ₑ) (Complex.polarCoord.symm q) ≤ box q := by
          intro q hq
          simp only [hbox]
          rw [polarCoord_target, Set.mem_prod] at hq
          obtain ⟨hq1, hq2⟩ := hq
          simp only [Set.mem_Ioi] at hq1
          by_cases hmem : Complex.polarCoord.symm q ∈ Metric.closedBall (0 : ℂ) R₀
          · rw [Set.indicator_of_mem hmem]
            have hnorm : ‖Complex.polarCoord.symm q‖ = q.1 := by
              rw [Complex.norm_polarCoord_symm, abs_of_pos hq1]
            have hsymm_ne : Complex.polarCoord.symm q ≠ 0 := by
              rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hq1
            rw [enorm_inv hsymm_ne]
            have henorm : ‖Complex.polarCoord.symm q‖ₑ = ENNReal.ofReal q.1 := by
              rw [← ofReal_norm, hnorm]
            rw [henorm, smul_eq_mul,
              ENNReal.mul_inv_cancel
                (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq1)
                ENNReal.ofReal_lt_top.ne]
            have hqR : q.1 ≤ R₀ := by
              rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem; exact hmem
            rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hq1, hqR⟩, hq2⟩)]
          · rw [Set.indicator_of_notMem hmem]; simp
        calc
          ∫⁻ q in polarCoord.target, ENNReal.ofReal q.1 •
              (Metric.closedBall (0 : ℂ) R₀).indicator
                (fun w : ℂ => ‖w⁻¹‖ₑ) (Complex.polarCoord.symm q)
              ≤ ∫⁻ q in polarCoord.target, box q :=
                setLIntegral_mono (measurable_const.indicator
                  (measurableSet_Ioc.prod measurableSet_Ioo)) hbound
          _ ≤ ∫⁻ q, box q := setLIntegral_le_lintegral _ _
          _ = volume (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
                rw [hbox, lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
                simp
          _ < ⊤ := by
                rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc,
                  Real.volume_Ioo]
                exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      have hCT : cauchyTransform u
          = fun w => (-(1 / (Real.pi : ℂ))) • (MeasureTheory.convolution u k L volume) w := by
        funext w
        rw [cauchyTransform, MeasureTheory.convolution_def, smul_eq_mul]
        congr 1
        apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
        rw [hL, ContinuousLinearMap.mul_apply']
        change u ζ / (ζ - w) = u ζ * -(w - ζ)⁻¹
        have hflip : -(w - ζ)⁻¹ = (ζ - w)⁻¹ := by rw [← neg_sub ζ w, inv_neg, neg_neg]
        rw [hflip, div_eq_mul_inv]
      rw [hCT]
      exact (hucs.contDiff_convolution_left L hu hk_loc).const_smul _
    have hPC1 : ContDiffOn ℝ 1 (cauchyTransform u) Set.univ := by
      rw [contDiffOn_univ]
      exact hF.of_le (by exact_mod_cast le_top)
    have hDz : ∀ z, dz (cauchyTransform u) z = beurling u z := fun z =>
      beurling_eq_dz_cauchyTransform hu1 hucs z
    have hDzbar : ∀ z, dzbar (cauchyTransform u) z = u z := fun z =>
      dzbar_cauchyTransform hu1 hucs z
    constructor
    · have h1 := HasWeakDirDeriv.of_contDiffOn (v := 1) isOpen_univ hPC1
      have heq : (fun z => (fderiv ℝ (cauchyTransform u) z) 1)
          = fun z => beurling u z + u z := by
        funext z
        have e1 := hDz z
        have e2 := hDzbar z
        simp only [dz] at e1
        simp only [dzbar] at e2
        linear_combination e1 + e2
      rwa [heq] at h1
    · have h1 := HasWeakDirDeriv.of_contDiffOn (v := Complex.I) isOpen_univ hPC1
      have heq : (fun z => (fderiv ℝ (cauchyTransform u) z) Complex.I)
          = fun z => Complex.I * (beurling u z - u z) := by
        funext z
        have e1 := hDz z
        have e2 := hDzbar z
        simp only [dz] at e1
        simp only [dzbar] at e2
        linear_combination Complex.I * e1 - Complex.I * e2
          + ((fderiv ℝ (cauchyTransform u) z) Complex.I) * Complex.I_sq
      rwa [heq] at h1
  -- ===== PART 6: locally uniform convergence of the transforms =====
  have hPwb : ∀ (w : ℂ → ℂ), MemLp w p volume → (∀ ζ : ℂ, ρ < ‖ζ‖ → w ζ = 0) →
      ∀ (T : ℝ), 0 ≤ T → ∀ z : ℂ, ‖z‖ ≤ T →
      ‖cauchyTransform w z‖
        ≤ 1/Real.pi * (((2*Real.pi/(2-qr)) * (ρ+T+1)^(2-qr))^(1/qr)
            * (eLpNorm w p volume).toReal) := by
    intro w hw hwsupp T hT z hzT
    have hBsub : B ⊆ Metric.ball z (ρ+T+1) := by
      intro ζ hζ
      rw [hB_def, Metric.mem_closedBall, dist_zero_right] at hζ
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖ζ - z‖ ≤ ‖ζ‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ ρ + T := by linarith
        _ < ρ + T + 1 := by linarith
    have hCnn : (0:ℝ) ≤ (2*Real.pi/(2-qr)) * (ρ+T+1)^(2-qr) :=
      mul_nonneg (div_nonneg (by positivity) (by linarith))
        (Real.rpow_nonneg (by linarith) _)
    have hmain : ‖∫ ζ, w ζ / (ζ - z)‖ₑ
        ≤ eLpNorm w p volume
            * ENNReal.ofReal ((2*Real.pi/(2-qr)) * (ρ+T+1)^(2-qr)) ^ (1/qr) := by
      calc ‖∫ ζ, w ζ / (ζ - z)‖ₑ
          ≤ ∫⁻ ζ, ‖w ζ / (ζ - z)‖ₑ := enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ ζ, ‖w ζ‖ₑ * ‖(ζ - z)⁻¹‖ₑ := lintegral_congr fun ζ => by
            rw [div_eq_mul_inv, enorm_mul]
        _ = ∫⁻ ζ in B, ‖w ζ‖ₑ * ‖(ζ - z)⁻¹‖ₑ := by
            rw [← lintegral_indicator hBmeas]
            apply lintegral_congr
            intro ζ
            by_cases hζ : ζ ∈ B
            · rw [Set.indicator_of_mem hζ]
            · rw [Set.indicator_of_notMem hζ]
              have hw0 : w ζ = 0 := hwsupp ζ (by
                simpa [hB_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ)
              rw [hw0]
              simp
        _ ≤ (∫⁻ ζ in B, ‖w ζ‖ₑ ^ pr) ^ (1/pr) * (∫⁻ ζ in B, ‖(ζ - z)⁻¹‖ₑ ^ qr) ^ (1/qr) :=
            ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq (hw.1.restrict.enorm)
              (((measurable_id.sub_const z).inv).enorm.aemeasurable.restrict)
        _ ≤ eLpNorm w p volume
              * ENNReal.ofReal ((2*Real.pi/(2-qr)) * (ρ+T+1)^(2-qr)) ^ (1/qr) := by
            refine mul_le_mul' ?_ (ENNReal.rpow_le_rpow ?_ (le_of_lt (one_div_pos.mpr hqr0)))
            · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']
              exact ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _)
                (le_of_lt (one_div_pos.mpr hpr0))
            · exact le_trans (lintegral_mono_set hBsub) (hballE z (ρ+T+1) (by linarith))
    rw [cauchyTransform, norm_mul, hconst]
    have hconv : eLpNorm w p volume
          * ENNReal.ofReal ((2*Real.pi/(2-qr)) * (ρ+T+1)^(2-qr)) ^ (1/qr)
        = ENNReal.ofReal (((2*Real.pi/(2-qr)) * (ρ+T+1)^(2-qr))^(1/qr)
            * (eLpNorm w p volume).toReal) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hCnn (le_of_lt (one_div_pos.mpr hqr0)),
        ENNReal.ofReal_mul (Real.rpow_nonneg hCnn _), ENNReal.ofReal_toReal hw.2.ne,
        mul_comm]
    rw [hconv] at hmain
    have hXle : ‖∫ ζ, w ζ / (ζ - z)‖
        ≤ ((2*Real.pi/(2-qr)) * (ρ+T+1)^(2-qr))^(1/qr) * (eLpNorm w p volume).toReal := by
      rw [← ofReal_norm] at hmain
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg (Real.rpow_nonneg hCnn _) ENNReal.toReal_nonneg)).mp hmain
    exact mul_le_mul_of_nonneg_left hXle (by positivity)
  have hUnif : TendstoLocallyUniformly (fun n => cauchyTransform (hseq n))
      (cauchyTransform h) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := hK.isBounded.subset_closedBall 0
    set T : ℝ := max T₀ 0 with hT_def
    have hT0 : 0 ≤ T := le_max_right _ _
    set κT : ℝ := ((2*Real.pi/(2-qr)) * (ρ+T+1)^(2-qr))^(1/qr) with hκT_def
    have hκT0 : 0 ≤ κT := Real.rpow_nonneg
      (mul_nonneg (div_nonneg (by positivity) (by linarith))
        (Real.rpow_nonneg (by linarith) _)) _
    have hC0 : (0:ℝ) < 1/Real.pi * κT + 1 := by positivity
    have hev := hδp.eventually_lt_const
      (show (0:ℝ) < ε / (1/Real.pi * κT + 1) by positivity)
    filter_upwards [hev] with n hn
    intro z hzK
    have hzT : ‖z‖ ≤ T := by
      have := hT₀ hzK
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact le_trans this (le_max_left _ _)
    have hwsupp : ∀ ζ : ℂ, ρ < ‖ζ‖ → h ζ - hseq n ζ = 0 := by
      intro ζ hζ
      rw [hsuppρ ζ hζ, hseqsupp n ζ hζ, sub_zero]
    have hdiff : cauchyTransform h z - cauchyTransform (hseq n) z
        = cauchyTransform (fun ζ => h ζ - hseq n ζ) z := by
      rw [cauchyTransform, cauchyTransform, cauchyTransform, ← mul_sub]
      congr 1
      rw [← integral_sub (hCT1 hh hsupp z) (hCT1 (hseqLp n) (hseqsupp n) z)]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ζ
      simp only [sub_div]
    rw [dist_eq_norm, hdiff]
    set δ : ℝ := (eLpNorm (fun ζ => h ζ - hseq n ζ) p volume).toReal with hδ_def
    have hδnn : 0 ≤ δ := ENNReal.toReal_nonneg
    calc ‖cauchyTransform (fun ζ => h ζ - hseq n ζ) z‖
        ≤ 1/Real.pi * (κT * δ) :=
          hPwb _ (hh.sub (hseqLp n)) hwsupp T hT0 z hzT
      _ = (1/Real.pi * κT) * δ := by ring
      _ ≤ (1/Real.pi * κT + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδnn
      _ < (1/Real.pi * κT + 1) * (ε / (1/Real.pi * κT + 1)) :=
          mul_lt_mul_of_pos_left hn hC0
      _ = ε := by field_simp
  -- ===== PART 7: weak-L² convergence of the gradient components =====
  have hbeurl_sub : ∀ (f g : ℂ → ℂ), MemLp f 2 volume → MemLp g 2 volume →
      eLpNorm (fun z => beurling f z - beurling g z) 2 volume
        = eLpNorm (fun z => f z - g z) 2 volume := by
    intro f g hf hg
    have h1 : (fun z => beurling f z - beurling g z) =ᵐ[volume] beurling (f - g) :=
      (beurling_sub_ae hf hg).symm
    rw [eLpNorm_congr_ae h1, beurling_l2_isometry (hf.sub hg)]
    rfl
  have hweak_gen : ∀ (Gn : ℕ → ℂ → ℂ) (G : ℂ → ℂ),
      (∀ n, MemLp (Gn n) 2 volume) → MemLp G 2 volume →
      (∀ n, eLpNorm (fun z => Gn n z - G z) 2 volume
        ≤ 2 * eLpNorm (fun z => hseq n z - h z) 2 volume) →
      TendstoWeaklyL2Loc Gn G := by
    intro Gn G hGn hG hGb ψ hψ _hψcs
    rw [tendsto_iff_dist_tendsto_zero]
    have hbnd : ∀ n : ℕ, dist (∫ z, Gn n z * ψ z) (∫ z, G z * ψ z)
        ≤ 2 * (eLpNorm (fun z => hseq n z - h z) 2 volume).toReal
            * (eLpNorm ψ 2 volume).toReal := by
      intro n
      rw [dist_eq_norm, ← integral_sub (hintpair _ _ (hGn n) hψ) (hintpair _ _ hG hψ)]
      have hcongr : (fun z => Gn n z * ψ z - G z * ψ z)
          = fun z => (Gn n z - G z) * ψ z := by
        funext z
        ring
      rw [hcongr]
      calc ‖∫ z, (Gn n z - G z) * ψ z‖
          ≤ (eLpNorm (fun z => Gn n z - G z) 2 volume).toReal
              * (eLpNorm ψ 2 volume).toReal := hpair _ _ ((hGn n).sub hG) hψ
        _ ≤ 2 * (eLpNorm (fun z => hseq n z - h z) 2 volume).toReal
              * (eLpNorm ψ 2 volume).toReal := by
            apply mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
            have hfin : (2 : ℝ≥0∞) * eLpNorm (fun z => hseq n z - h z) 2 volume ≠ ⊤ :=
              ENNReal.mul_ne_top ENNReal.ofNat_ne_top ((hseqL2 n).sub hL2h).2.ne
            have h2 := ENNReal.toReal_mono hfin (hGb n)
            rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h2
    have hmaj : Tendsto (fun n : ℕ =>
        2 * (eLpNorm (fun z => hseq n z - h z) 2 volume).toReal
          * (eLpNorm ψ 2 volume).toReal) atTop (𝓝 0) := by
      have := (hδ2.const_mul 2).mul_const (eLpNorm ψ 2 volume).toReal
      simpa using this
    exact squeeze_zero (fun n => dist_nonneg) hbnd hmaj
  have hGdiff1 : ∀ n, eLpNorm
      (fun z => (beurling (hseq n) z + hseq n z) - (beurling h z + h z)) 2 volume
      ≤ 2 * eLpNorm (fun z => hseq n z - h z) 2 volume := by
    intro n
    have hptw : (fun z => (beurling (hseq n) z + hseq n z) - (beurling h z + h z))
        = fun z => (beurling (hseq n) z - beurling h z) + (hseq n z - h z) := by
      funext z
      ring
    rw [hptw]
    calc eLpNorm (fun z => (beurling (hseq n) z - beurling h z) + (hseq n z - h z)) 2 volume
        ≤ eLpNorm (fun z => beurling (hseq n) z - beurling h z) 2 volume
            + eLpNorm (fun z => hseq n z - h z) 2 volume :=
          eLpNorm_add_le
            ((memLp_beurling (hseqL2 n)).sub (memLp_beurling hL2h)).aestronglyMeasurable
            ((hseqL2 n).sub hL2h).aestronglyMeasurable (by norm_num)
      _ ≤ eLpNorm (fun z => hseq n z - h z) 2 volume
            + eLpNorm (fun z => hseq n z - h z) 2 volume :=
          add_le_add (le_of_eq (hbeurl_sub _ _ (hseqL2 n) hL2h)) le_rfl
      _ = 2 * eLpNorm (fun z => hseq n z - h z) 2 volume := (two_mul _).symm
  have hGdiffI : ∀ n, eLpNorm
      (fun z => Complex.I * (beurling (hseq n) z - hseq n z)
        - Complex.I * (beurling h z - h z)) 2 volume
      ≤ 2 * eLpNorm (fun z => hseq n z - h z) 2 volume := by
    intro n
    have hptw : (fun z => Complex.I * (beurling (hseq n) z - hseq n z)
          - Complex.I * (beurling h z - h z))
        = fun z => Complex.I
            • ((beurling (hseq n) z - beurling h z) - (hseq n z - h z)) := by
      funext z
      simp only [smul_eq_mul]
      ring
    rw [hptw]
    calc eLpNorm (fun z => Complex.I
          • ((beurling (hseq n) z - beurling h z) - (hseq n z - h z))) 2 volume
        = ‖Complex.I‖ₑ * eLpNorm
            (fun z => (beurling (hseq n) z - beurling h z) - (hseq n z - h z)) 2 volume :=
          eLpNorm_const_smul Complex.I
            (fun z => (beurling (hseq n) z - beurling h z) - (hseq n z - h z)) 2 volume
      _ = eLpNorm
            (fun z => (beurling (hseq n) z - beurling h z) - (hseq n z - h z)) 2 volume := by
          rw [show ‖Complex.I‖ₑ = 1 by
            rw [← ofReal_norm, Complex.norm_I, ENNReal.ofReal_one], one_mul]
      _ ≤ eLpNorm (fun z => beurling (hseq n) z - beurling h z) 2 volume
            + eLpNorm (fun z => hseq n z - h z) 2 volume :=
          eLpNorm_sub_le
            ((memLp_beurling (hseqL2 n)).sub (memLp_beurling hL2h)).aestronglyMeasurable
            ((hseqL2 n).sub hL2h).aestronglyMeasurable (by norm_num)
      _ ≤ eLpNorm (fun z => hseq n z - h z) 2 volume
            + eLpNorm (fun z => hseq n z - h z) 2 volume :=
          add_le_add (le_of_eq (hbeurl_sub _ _ (hseqL2 n) hL2h)) le_rfl
      _ = 2 * eLpNorm (fun z => hseq n z - h z) 2 volume := (two_mul _).symm
  have hweak1 : TendstoWeaklyL2Loc (fun n z => beurling (hseq n) z + hseq n z)
      (fun z => beurling h z + h z) :=
    hweak_gen _ _ (fun n => (memLp_beurling (hseqL2 n)).add (hseqL2 n))
      ((memLp_beurling hL2h).add hL2h) hGdiff1
  have hweakI : TendstoWeaklyL2Loc
      (fun n z => Complex.I * (beurling (hseq n) z - hseq n z))
      (fun z => Complex.I * (beurling h z - h z)) := by
    refine hweak_gen _ _ (fun n => ?_) ?_ hGdiffI
    · have := ((memLp_beurling (hseqL2 n)).sub (hseqL2 n)).const_mul Complex.I
      simpa using this
    · have := ((memLp_beurling hL2h).sub hL2h).const_mul Complex.I
      simpa using this
  -- ===== PART 8: assemble =====
  constructor
  · exact hasWeakDirDeriv_of_tendsto hUnif
      (fun n => hCT3 (hseqLp n) (hseqsupp n)) (hCT3 hh hsupp)
      (gxₙ := fun n z => beurling (hseq n) z + hseq n z)
      (fun n => (hsmoothgrad (hseq n) (hseqsm n) (hseqcs n)).1) hweak1
  · exact hasWeakDirDeriv_of_tendsto hUnif
      (fun n => hCT3 (hseqLp n) (hseqsupp n)) (hCT3 hh hsupp)
      (gxₙ := fun n z => Complex.I * (beurling (hseq n) z - hseq n z))
      (fun n => (hsmoothgrad (hseq n) (hseqsm n) (hseqcs n)).2) hweakI

/-- **The classical-arrangement fixed point `h = μ·S h + g` in `Lᵖ`.** For a
measurable, essentially bounded multiplier `μ` and exponent data making
`u ↦ μ·S u` a contraction (`‖μ‖∞·C < 1` with `C` a Calderón–Zygmund bound for the
Beurling transform at `p`), every datum `g ∈ Lᵖ` produces a solution `h ∈ Lᵖ` of

`h = μ·S h + g` (a.e.),

with the geometric-series norm bound. The datum is kept general: `g = μ` yields the
principal-solution field, and the auxiliary data of the injectivity and holomorphic-
dependence arguments reuse the same solve. Mirrors the conjugate-arrangement solve
`exists_memLp_solution_of_beltrami_fixedPoint` via `ContractingWith.fixedPoint` on
`Lp ℂ p volume`. -/
theorem exists_lp_fixedPoint_beltrami {μ g : ℂ → ℂ} {p : ℝ≥0∞} {C : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤) (hμmeas : Measurable μ)
    (hμfin : eLpNormEssSup μ volume ≠ ⊤)
    (hCb : IsCalderonZygmundBound beurling p C)
    (hcontr : (eLpNormEssSup μ volume).toReal * C < 1)
    (hg : MemLp g p volume) :
    ∃ h : ℂ → ℂ, MemLp h p volume ∧
      h =ᵐ[volume] (fun z => μ z * beurling h z + g z) ∧
      eLpNorm h p volume
        ≤ ENNReal.ofReal ((1 - (eLpNormEssSup μ volume).toReal * C)⁻¹)
          * eLpNorm g p volume := by
  classical
  -- Basic facts about `p` and the CZ constant.
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_of_lt (lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hp)
  have : Fact (1 ≤ p) := ⟨hp1⟩
  obtain ⟨hC0, hCbound⟩ := hCb
  set k : ℝ := (eLpNormEssSup μ volume).toReal with hk_def
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hμtop : eLpNormEssSup μ volume ≠ ⊤ := hμfin
  -- `μ` is essentially bounded: `MemLp μ ⊤`.
  have hμLinf : MemLp μ ⊤ volume := by
    refine ⟨hμmeas.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_exponent_top]
    exact lt_of_le_of_ne le_top hμtop
  -- The multiplier preserves `Lᵖ`.
  have hμmul : ∀ {u : ℂ → ℂ}, MemLp u p volume → MemLp (fun z => μ z * u z) p volume :=
    fun {u} hu => hu.mul' hμLinf
  -- Beurling sends `Lᵖ` to `Lᵖ`.
  have hbeurLp : ∀ {u : ℂ → ℂ}, MemLp u p volume → MemLp (beurling u) p volume :=
    fun {u} hu => memLp_beurling_of_memLp hp hp' hu
  -- The operator `S u := μ · (beurling u)` sends `Lᵖ` to `Lᵖ` (`MemLp`).
  have hSmem : ∀ {u : ℂ → ℂ}, MemLp u p volume →
      MemLp (fun z => μ z * beurling u z) p volume :=
    fun {u} hu => hμmul (hbeurLp hu)
  -- `eLpNormEssSup μ = ENNReal.ofReal k`.
  have hessSup_eq : eLpNormEssSup μ volume = ENNReal.ofReal k := by
    rw [hk_def, ENNReal.ofReal_toReal hμtop]
  -- Quantitative contraction estimate for `S u = μ · (beurling u)`:
  -- `eLpNorm (μ · beurling u) p ≤ ofReal (k*C) * eLpNorm u p`.
  have hSeLp : ∀ {u : ℂ → ℂ}, MemLp u p volume →
      eLpNorm (fun z => μ z * beurling u z) p volume
        ≤ ENNReal.ofReal (k * C) * eLpNorm u p volume := by
    intro u hu
    calc eLpNorm (fun z => μ z * beurling u z) p volume
        ≤ eLpNormEssSup μ volume * eLpNorm (beurling u) p volume :=
          eLpNorm_mul_le_essSup_mul hμmeas.aestronglyMeasurable (hbeurLp hu)
      _ ≤ ENNReal.ofReal k * (ENNReal.ofReal C * eLpNorm u p volume) := by
          rw [hessSup_eq]; gcongr; exact hCbound u hu
      _ = ENNReal.ofReal (k * C) * eLpNorm u p volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hk0]
  -- Beurling subtractivity on `Lᵖ` (a corollary of additivity L4').
  have hbeurling_sub : ∀ {u v : ℂ → ℂ}, MemLp u p volume → MemLp v p volume →
      beurling (fun w => u w - v w) =ᵐ[volume] beurling u - beurling v := by
    intro u v hu hv
    have hadd := beurling_add_ae_lp hp hp' hv (show MemLp (fun w => u w - v w) p volume from
      hu.sub hv)
    -- `v + (u - v) = u`.
    have hvuv : ((v : ℂ → ℂ) + fun w => u w - v w) = u := by funext w; simp
    rw [hvuv] at hadd
    -- so `beurling u =ᵐ beurling v + beurling (u - v)`.
    filter_upwards [hadd] with z hz
    simp only [Pi.add_apply, Pi.sub_apply] at hz ⊢
    rw [hz]; ring
  -- The contraction factor `K := (k·C).toNNReal < 1`.
  set K : ℝ≥0 := (k * C).toNNReal with hK_def
  have hkC0 : 0 ≤ k * C := mul_nonneg hk0 hC0
  have hKlt : K < 1 := by rw [hK_def, Real.toNNReal_lt_one]; exact hcontr
  have hKcoe : (K : ℝ≥0∞) = ENNReal.ofReal (k * C) := rfl
  -- The affine self-map `Φ` of `Lᵖ` whose fixed point solves the equation.
  set Φ : Lp ℂ p volume → Lp ℂ p volume :=
    fun H => MemLp.toLp _ (hSmem (Lp.memLp H)) + MemLp.toLp g hg with hΦ_def
  -- `Φ` is `K`-Lipschitz: pass through `coeFn` and the contraction estimate.
  have hΦlip : LipschitzWith K Φ := by
    intro x y
    -- `Φ x - Φ y = (μ·beurling x).toLp - (μ·beurling y).toLp` (the constant cancels).
    have hdiff : ⇑(Φ x) - ⇑(Φ y)
        =ᵐ[volume] ⇑(MemLp.toLp _ (hSmem (Lp.memLp x)))
          - ⇑(MemLp.toLp _ (hSmem (Lp.memLp y))) := by
      simp only [hΦ_def]
      filter_upwards [Lp.coeFn_add (MemLp.toLp _ (hSmem (Lp.memLp x))) (MemLp.toLp g hg),
        Lp.coeFn_add (MemLp.toLp _ (hSmem (Lp.memLp y))) (MemLp.toLp g hg)] with z h1 h2
      simp only [Pi.sub_apply, h1, h2, Pi.add_apply]; ring
    -- a.e. identity: this difference equals `μ · beurling (x - y)` a.e.
    have hcoe : (⇑(MemLp.toLp _ (hSmem (Lp.memLp x)))
          - ⇑(MemLp.toLp _ (hSmem (Lp.memLp y))) : ℂ → ℂ)
        =ᵐ[volume]
          fun w => μ w * beurling (fun v => (x : ℂ → ℂ) v - (y : ℂ → ℂ) v) w := by
      -- `μ·beurling x - μ·beurling y = μ·(beurling x - beurling y) =ᵐ μ·beurling (x-y)`.
      have hbsub := hbeurling_sub (Lp.memLp x) (Lp.memLp y)
      filter_upwards [MemLp.coeFn_toLp (hSmem (Lp.memLp x)),
        MemLp.coeFn_toLp (hSmem (Lp.memLp y)), hbsub] with z hzx hzy hzb
      simp only [Pi.sub_apply] at hzx hzy ⊢
      rw [hzx, hzy, hzb]
      simp only [Pi.sub_apply]
      ring
    -- Compute the `edist`s as `eLpNorm`s and apply the contraction estimate.
    rw [Lp.edist_def, Lp.edist_def, eLpNorm_congr_ae hdiff, eLpNorm_congr_ae hcoe, hKcoe]
    calc eLpNorm (fun w => μ w * beurling (fun v => (x : ℂ → ℂ) v - (y : ℂ → ℂ) v) w) p volume
        ≤ ENNReal.ofReal (k * C)
            * eLpNorm (fun v => (x : ℂ → ℂ) v - (y : ℂ → ℂ) v) p volume :=
          hSeLp ((Lp.memLp x).sub (Lp.memLp y))
      _ = ENNReal.ofReal (k * C) * eLpNorm (⇑x - ⇑y) p volume := rfl
  -- The contraction `Φ` has a fixed point `H₀ ∈ Lᵖ` in the complete space `Lᵖ`.
  have hΦcontr : ContractingWith K Φ := ⟨hKlt, hΦlip⟩
  set H₀ : Lp ℂ p volume := hΦcontr.fixedPoint Φ with hH₀_def
  have hfix : Φ H₀ = H₀ := hΦcontr.fixedPoint_isFixedPt
  -- From `Φ H₀ = H₀`: `H₀ =ᵐ μ·(beurling H₀) + g`.
  have haeeq : (H₀ : ℂ → ℂ) =ᵐ[volume]
      fun z => μ z * beurling (⇑H₀) z + g z := by
    have hval : (MemLp.toLp _ (hSmem (Lp.memLp H₀)) + MemLp.toLp g hg : Lp ℂ p volume)
        = H₀ := hfix
    calc (H₀ : ℂ → ℂ)
        =ᵐ[volume] ⇑(MemLp.toLp _ (hSmem (Lp.memLp H₀)) + MemLp.toLp g hg) := by
          rw [hval]
      _ =ᵐ[volume] ⇑(MemLp.toLp _ (hSmem (Lp.memLp H₀))) + ⇑(MemLp.toLp g hg) :=
          Lp.coeFn_add _ _
      _ =ᵐ[volume] fun z => μ z * beurling (⇑H₀) z + g z := by
          filter_upwards [MemLp.coeFn_toLp (hSmem (Lp.memLp H₀)), MemLp.coeFn_toLp hg]
            with z hzS hzg
          simp only [Pi.add_apply, hzS, hzg]
  refine ⟨⇑H₀, Lp.memLp H₀, haeeq, ?_⟩
  -- The geometric-series norm bound. Both `eLpNorm`s are finite.
  have hEfin : eLpNorm (⇑H₀) p volume ≠ ⊤ := (Lp.memLp H₀).2.ne
  have hGfin : eLpNorm g p volume ≠ ⊤ := hg.2.ne
  -- Triangle inequality + the contraction estimate: `E ≤ ofReal (k·C)·E + G`.
  have hE_le : eLpNorm (⇑H₀) p volume
      ≤ ENNReal.ofReal (k * C) * eLpNorm (⇑H₀) p volume + eLpNorm g p volume := by
    calc eLpNorm (⇑H₀) p volume
        = eLpNorm (fun z => μ z * beurling (⇑H₀) z + g z) p volume :=
          eLpNorm_congr_ae haeeq
      _ ≤ eLpNorm (fun z => μ z * beurling (⇑H₀) z) p volume + eLpNorm g p volume :=
          eLpNorm_add_le (hSmem (Lp.memLp H₀)).aestronglyMeasurable
            hg.aestronglyMeasurable hp1
      _ ≤ ENNReal.ofReal (k * C) * eLpNorm (⇑H₀) p volume + eLpNorm g p volume := by
          gcongr
          exact hSeLp (Lp.memLp H₀)
  -- Pass to real numbers to rearrange (`⊤`-free by finiteness).
  have hmul_ne : ENNReal.ofReal (k * C) * eLpNorm (⇑H₀) p volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEfin
  have hreal : (eLpNorm (⇑H₀) p volume).toReal
      ≤ k * C * (eLpNorm (⇑H₀) p volume).toReal + (eLpNorm g p volume).toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hmul_ne, hGfin⟩) hE_le
    rwa [ENNReal.toReal_add hmul_ne hGfin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hkC0] at this
  have h1pos : 0 < 1 - k * C := by linarith
  have hreal2 : (eLpNorm (⇑H₀) p volume).toReal
      ≤ (1 - k * C)⁻¹ * (eLpNorm g p volume).toReal := by
    rw [inv_mul_eq_div, le_div_iff₀ h1pos]
    nlinarith [hreal]
  -- Return to `ℝ≥0∞`.
  calc eLpNorm (⇑H₀) p volume
      = ENNReal.ofReal (eLpNorm (⇑H₀) p volume).toReal :=
        (ENNReal.ofReal_toReal hEfin).symm
    _ ≤ ENNReal.ofReal ((1 - k * C)⁻¹ * (eLpNorm g p volume).toReal) :=
        ENNReal.ofReal_le_ofReal hreal2
    _ = ENNReal.ofReal ((1 - k * C)⁻¹) * ENNReal.ofReal (eLpNorm g p volume).toReal :=
        ENNReal.ofReal_mul (inv_nonneg.2 h1pos.le)
    _ = ENNReal.ofReal ((1 - k * C)⁻¹) * eLpNorm g p volume := by
        rw [ENNReal.ofReal_toReal hGfin]

/-- **The principal solution of the Beltrami equation** for a coefficient `b`: a map
of the form `f = id + P h`, where `h` is an `Lᵖ` (`p > 2`) fixed point of
`u ↦ b.μ·S u + b.μ` vanishing outside a ball. The bundle records exactly the
Neumann-series construction; continuity, decay, `W^{1,2}_loc` membership, and the
weak Beltrami equation are derived in the property lemmas below, and the
homeomorphism/orientation upgrades live in `QC/MRMT/Existence.lean`. -/
def IsPrincipalSolution (b : BeltramiCoeff) (f : ℂ → ℂ) : Prop :=
  ∃ (p : ℝ≥0∞) (h : ℂ → ℂ) (R : ℝ), 2 < p ∧ p ≠ ⊤ ∧ MemLp h p volume ∧
    (∀ z : ℂ, R < ‖z‖ → h z = 0) ∧
    h =ᵐ[volume] (fun z => b.μ z * beurling h z + b.μ z) ∧
    ∀ z : ℂ, f z = z + cauchyTransform h z

/-- **Existence of the principal solution** for a compactly vanishing coefficient:
choose `p > 2` with `‖μ‖∞·‖S‖ₚ < 1` (`exists_p_gt_two_beurling_contraction`), solve
the fixed-point equation with datum `μ` (`exists_lp_fixedPoint_beltrami`), correct
the fixed point on a null set so it vanishes exactly where `μ` does, and set
`f = id + P h`. -/
theorem exists_isPrincipalSolution (b : BeltramiCoeff) {R : ℝ}
    (hsupp : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0) :
    ∃ f : ℂ → ℂ, IsPrincipalSolution b f := by
  -- Contraction exponent data.
  obtain ⟨p, hp2, hptop, C, hCb, hcontr⟩ :=
    exists_p_gt_two_beurling_contraction b.measurable b.bound
  have hμfin : eLpNormEssSup b.μ volume ≠ ⊤ := (lt_trans b.bound ENNReal.one_lt_top).ne
  -- The coefficient is `Lᵖ`.
  have hμLp : MemLp b.μ p volume :=
    memLp_of_eLpNormEssSup_ne_top_of_support hptop b.measurable hμfin hsupp
  -- The fixed point with datum `g = b.μ`.
  obtain ⟨h, hLp, haeeq, _hbound⟩ :=
    exists_lp_fixedPoint_beltrami hp2 hptop b.measurable hμfin hCb hcontr hμLp
  -- The everywhere-defined representative, vanishing pointwise outside the ball.
  set h' : ℂ → ℂ := fun z => b.μ z * beurling h z + b.μ z with hh'_def
  have hh'ae : h' =ᵐ[volume] h := haeeq.symm
  have hh'Lp : MemLp h' p volume := hLp.ae_eq haeeq
  have hh'supp : ∀ z : ℂ, R < ‖z‖ → h' z = 0 := by
    intro z hz
    simp only [hh'_def]
    rw [hsupp z hz, zero_mul, zero_add]
  -- `L²` memberships (finite-measure embedding on the support ball).
  have hL2h' : MemLp h' 2 volume := by
    set m : ℝ := max R 0 with hm_def
    set B : Set ℂ := Metric.closedBall (0:ℂ) m with hB_def
    have hBmeas : MeasurableSet B := by rw [hB_def]; exact measurableSet_closedBall
    have : IsFiniteMeasure (volume.restrict B) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (isCompact_closedBall _ _).measure_lt_top⟩
    have hind : h' = B.indicator h' := by
      funext ζ
      by_cases hζ : ζ ∈ B
      · rw [Set.indicator_of_mem hζ]
      · rw [Set.indicator_of_notMem hζ]
        refine hh'supp ζ ?_
        have hm : m < ‖ζ‖ := by
          simpa [hB_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
        exact lt_of_le_of_lt (le_max_left R 0) hm
    rw [hind]
    exact (memLp_indicator_iff_restrict hBmeas).2 ((hh'Lp.restrict B).mono_exponent hp2.le)
  have hL2h : MemLp h 2 volume := hL2h'.ae_eq hh'ae
  -- The fixed-point equation transfers to `h'`.
  have hSeq : beurling h =ᵐ[volume] beurling h' := beurling_congr_ae hL2h hL2h' haeeq
  have heq' : h' =ᵐ[volume] (fun z => b.μ z * beurling h' z + b.μ z) := by
    filter_upwards [hSeq] with z hz
    rw [← hz]
  exact ⟨fun z => z + cauchyTransform h' z, p, h', R, hp2, hptop, hh'Lp, hh'supp, heq',
    fun z => rfl⟩

/-- A principal solution is continuous. -/
theorem IsPrincipalSolution.continuous {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) : Continuous f := by
  obtain ⟨p, h, R, hp, hp', hmem, hsupp, _heq, hrepr⟩ := hf
  have hfeq : f = fun z => z + cauchyTransform h z := funext hrepr
  rw [hfeq]
  exact continuous_id.add
    (continuous_cauchyTransform_of_memLp_of_support hp hp' hmem hsupp)

/-- A principal solution is normalized at infinity: `f(z) − z → 0` as `z → ∞`. -/
theorem IsPrincipalSolution.tendsto_sub_id_cocompact {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) :
    Tendsto (fun z => f z - z) (Filter.cocompact ℂ) (𝓝 0) := by
  obtain ⟨p, h, R, hp, hp', hmem, hsupp, _heq, hrepr⟩ := hf
  have hfeq : (fun z => f z - z) = cauchyTransform h := by
    funext z
    rw [hrepr z]
    ring
  rw [hfeq]
  exact cauchyTransform_tendsto_cocompact hp hp' hmem hsupp

/-- **The weak gradient of a principal solution**: `f = id + P h` has weak coordinate
partials `1 + (S h + h)` and `i·(1 + S h − h)` — the identity contributes `(1, i)`
and the potential contributes the Cauchy-transform gradient. -/
theorem IsPrincipalSolution.hasWeakGradient {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) :
    ∃ (p : ℝ≥0∞) (h : ℂ → ℂ), 2 < p ∧ p ≠ ⊤ ∧ MemLp h p volume ∧
      h =ᵐ[volume] (fun z => b.μ z * beurling h z + b.μ z) ∧
      HasWeakGradient (fun z => 1 + (beurling h z + h z))
        (fun z => Complex.I * (1 + (beurling h z - h z))) f Set.univ ∧
      MemLpLocOn (fun z => 1 + (beurling h z + h z)) 2 Set.univ ∧
      MemLpLocOn (fun z => Complex.I * (1 + (beurling h z - h z))) 2 Set.univ := by
  obtain ⟨p, h, R, hp, hp', hmem, hsupp, heq, hrepr⟩ := hf
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_of_lt (lt_trans ENNReal.one_lt_two hp)
  have hSmem : MemLp (beurling h) p volume := memLp_beurling_of_memLp hp hp' hmem
  have hCT5 := hasWeakGradient_cauchyTransform hp hp' hmem hsupp
  have hPcont : Continuous (cauchyTransform h) :=
    continuous_cauchyTransform_of_memLp_of_support hp hp' hmem hsupp
  have hfeq : f = fun z => z + cauchyTransform h z := funext hrepr
  refine ⟨p, h, hp, hp', hmem, heq, ?_, ?_, ?_⟩
  · -- the weak gradient of `f = id + P h`
    have hid : ContDiffOn ℝ 1 (fun z : ℂ => z) Set.univ := contDiffOn_id
    have hid1 := HasWeakDirDeriv.of_contDiffOn (v := 1) isOpen_univ hid
    have hidI := HasWeakDirDeriv.of_contDiffOn (v := Complex.I) isOpen_univ hid
    have hfder1 : (fun z : ℂ => (fderiv ℝ (fun z : ℂ => z) z) 1) = fun _ : ℂ => (1:ℂ) := by
      funext z
      rw [fderiv_fun_id]
      rfl
    have hfderI : (fun z : ℂ => (fderiv ℝ (fun z : ℂ => z) z) Complex.I)
        = fun _ : ℂ => Complex.I := by
      funext z
      rw [fderiv_fun_id]
      rfl
    rw [hfder1] at hid1
    rw [hfderI] at hidI
    have hLIid : LocallyIntegrableOn (fun z : ℂ => z) Set.univ :=
      continuous_id.locallyIntegrable.locallyIntegrableOn _
    have hLIP : LocallyIntegrableOn (cauchyTransform h) Set.univ :=
      hPcont.locallyIntegrable.locallyIntegrableOn _
    have hLI1 : LocallyIntegrableOn (fun _ : ℂ => (1:ℂ)) Set.univ :=
      continuous_const.locallyIntegrable.locallyIntegrableOn _
    have hLII : LocallyIntegrableOn (fun _ : ℂ => Complex.I) Set.univ :=
      continuous_const.locallyIntegrable.locallyIntegrableOn _
    have hLIgx : LocallyIntegrableOn (fun z => beurling h z + h z) Set.univ :=
      ((hSmem.add hmem).locallyIntegrable hp1).locallyIntegrableOn _
    have hLIgy : LocallyIntegrableOn (fun z => Complex.I * (beurling h z - h z))
        Set.univ :=
      (((hSmem.sub hmem).const_mul Complex.I).locallyIntegrable hp1).locallyIntegrableOn _
    constructor
    · have hadd := HasWeakDirDeriv.add hid1 hCT5.1 hLIid hLIP hLI1 hLIgx
      rw [hfeq]
      exact hadd
    · have hadd := HasWeakDirDeriv.add hidI hCT5.2 hLIid hLIP hLII hLIgy
      have hgy_eq : (fun z => Complex.I + Complex.I * (beurling h z - h z))
          = fun z => Complex.I * (1 + (beurling h z - h z)) := by
        funext z
        ring
      rw [hgy_eq] at hadd
      rw [hfeq]
      exact hadd
  · -- `gx` is locally `L²`
    intro K _ hKc
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    have h1 : MemLp (fun _ : ℂ => (1:ℂ)) 2 (volume.restrict K) := memLp_const _
    have h2 : MemLp (fun z => beurling h z + h z) 2 (volume.restrict K) :=
      ((hSmem.add hmem).restrict K).mono_exponent hp.le
    exact h1.add h2
  · -- `gy` is locally `L²`
    intro K _ hKc
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    have h1 : MemLp (fun _ : ℂ => (1:ℂ)) 2 (volume.restrict K) := memLp_const _
    have h2 : MemLp (fun z => beurling h z - h z) 2 (volume.restrict K) :=
      ((hSmem.sub hmem).restrict K).mono_exponent hp.le
    have h3 : MemLp (fun z => (1:ℂ) + (beurling h z - h z)) 2 (volume.restrict K) :=
      h1.add h2
    exact h3.const_mul Complex.I

/-- A principal solution is `W^{1,2}_loc`. -/
theorem IsPrincipalSolution.memW12loc {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) : MemW12loc f := by
  have hcont : Continuous f := hf.continuous
  obtain ⟨p, h, hp, hp', hmem, heq, hgrad, hgx, hgy⟩ := hf.hasWeakGradient
  refine ⟨?_, _, _, hgrad, hgx, hgy⟩
  intro K _ hKc
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  refine MemLp.of_bound hcont.aestronglyMeasurable.restrict C ?_
  filter_upwards [ae_restrict_mem hKc.measurableSet] with z hz
  exact hC z hz

/-- **The weak Beltrami equation for a principal solution**: the weak Wirtinger
parts of the gradient of `hf.hasWeakGradient` satisfy `∂̄f = μ·∂f` almost
everywhere — with `gx = 1 + S h + h` and `gy = i(1 + S h − h)`, the weak `∂̄`-part
`½(gx + i·gy) = h` and the weak `∂`-part `½(gx − i·gy) = 1 + S h`, and the fixed
point equation reads `h = μ·(1 + S h)`. -/
theorem IsPrincipalSolution.weak_beltrami {b : BeltramiCoeff} {f : ℂ → ℂ}
    (hf : IsPrincipalSolution b f) :
    ∃ u v : ℂ → ℂ, HasWeakGradient u v f Set.univ ∧
      MemLpLocOn u 2 Set.univ ∧ MemLpLocOn v 2 Set.univ ∧
      AEStronglyMeasurable u volume ∧ AEStronglyMeasurable v volume ∧
      ∀ᵐ z, (1 / 2 : ℂ) * (u z + Complex.I * v z)
        = b.μ z * ((1 / 2 : ℂ) * (u z - Complex.I * v z)) := by
  obtain ⟨p, h, hp, hp', hmem, heq, hgrad, hgx, hgy⟩ := hf.hasWeakGradient
  have hSmem : MemLp (beurling h) p volume := memLp_beurling_of_memLp hp hp' hmem
  refine ⟨fun z => 1 + (beurling h z + h z),
    fun z => Complex.I * (1 + (beurling h z - h z)), hgrad, hgx, hgy, ?_, ?_, ?_⟩
  · exact aestronglyMeasurable_const.add (hSmem.1.add hmem.1)
  · exact (aestronglyMeasurable_const.add (hSmem.1.sub hmem.1)).const_mul Complex.I
  · filter_upwards [heq] with z hz
    linear_combination hz
      + ((1 + beurling h z - h z) * (1 + b.μ z) / 2) * Complex.I_sq

/-- **Uniqueness of the principal solution.** Two principal solutions of the same
coefficient coincide: the difference of the two fixed-point fields solves the
homogeneous equation `δ = μ·S δ`, lies in `L²` (both fields vanish outside a ball
and are `L^{>2}`), and the `L²` isometry of the Beurling transform gives
`‖δ‖₂ ≤ ‖μ‖∞·‖δ‖₂`, forcing `δ = 0`; the Cauchy transforms then agree. -/
theorem isPrincipalSolution_unique {b : BeltramiCoeff} {f₁ f₂ : ℂ → ℂ}
    (h₁ : IsPrincipalSolution b f₁) (h₂ : IsPrincipalSolution b f₂) : f₁ = f₂ := by
  obtain ⟨p₁, k₁, R₁, hp₁, hp₁', hmem₁, hsupp₁, heq₁, hrepr₁⟩ := h₁
  obtain ⟨p₂, k₂, R₂, hp₂, hp₂', hmem₂, hsupp₂, heq₂, hrepr₂⟩ := h₂
  -- Both fixed-point fields are `L²` (finite-measure embedding on their support balls).
  have hL2 : ∀ (k : ℂ → ℂ) (p : ℝ≥0∞) (R : ℝ), 2 < p → MemLp k p volume →
      (∀ z : ℂ, R < ‖z‖ → k z = 0) → MemLp k 2 volume := by
    intro k p R hp hmem hsupp
    set m : ℝ := max R 0 with hm_def
    set B : Set ℂ := Metric.closedBall (0:ℂ) m with hB_def
    have hBmeas : MeasurableSet B := by rw [hB_def]; exact measurableSet_closedBall
    have : IsFiniteMeasure (volume.restrict B) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (isCompact_closedBall _ _).measure_lt_top⟩
    have hind : k = B.indicator k := by
      funext ζ
      by_cases hζ : ζ ∈ B
      · rw [Set.indicator_of_mem hζ]
      · rw [Set.indicator_of_notMem hζ]
        refine hsupp ζ ?_
        have hm : m < ‖ζ‖ := by
          simpa [hB_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
        exact lt_of_le_of_lt (le_max_left R 0) hm
    rw [hind]
    exact (memLp_indicator_iff_restrict hBmeas).2 ((hmem.restrict B).mono_exponent hp.le)
  have hk₁L2 : MemLp k₁ 2 volume := hL2 k₁ p₁ R₁ hp₁ hmem₁ hsupp₁
  have hk₂L2 : MemLp k₂ 2 volume := hL2 k₂ p₂ R₂ hp₂ hmem₂ hsupp₂
  have hδL2 : MemLp (k₁ - k₂) 2 volume := hk₁L2.sub hk₂L2
  -- The difference solves the homogeneous equation `δ = μ·S δ` a.e.
  have hSsub : beurling (k₁ - k₂) =ᵐ[volume] beurling k₁ - beurling k₂ :=
    beurling_sub_ae hk₁L2 hk₂L2
  have hδeq : (k₁ - k₂ : ℂ → ℂ)
      =ᵐ[volume] fun z => b.μ z * beurling (k₁ - k₂) z := by
    filter_upwards [heq₁, heq₂, hSsub] with z hz₁ hz₂ hzS
    have hzS' : beurling (k₁ - k₂) z = beurling k₁ z - beurling k₂ z := hzS
    simp only [Pi.sub_apply]
    rw [hz₁, hz₂, hzS']
    ring
  -- The `L²` isometry forces `‖δ‖₂ ≤ ‖μ‖∞·‖δ‖₂`, hence `δ = 0`.
  have hnorm : eLpNorm (k₁ - k₂) 2 volume
      ≤ eLpNormEssSup b.μ volume * eLpNorm (k₁ - k₂) 2 volume := by
    calc eLpNorm (k₁ - k₂) 2 volume
        = eLpNorm (fun z => b.μ z * beurling (k₁ - k₂) z) 2 volume :=
          eLpNorm_congr_ae hδeq
      _ ≤ eLpNormEssSup b.μ volume * eLpNorm (beurling (k₁ - k₂)) 2 volume :=
          eLpNorm_mul_le_essSup_mul b.measurable.aestronglyMeasurable
            (memLp_beurling hδL2)
      _ = eLpNormEssSup b.μ volume * eLpNorm (k₁ - k₂) 2 volume := by
          rw [beurling_l2_isometry hδL2]
  have hfin : eLpNorm (k₁ - k₂) 2 volume ≠ ⊤ := hδL2.2.ne
  have hzero : eLpNorm (k₁ - k₂) 2 volume = 0 := by
    by_contra h0
    have hlt : eLpNormEssSup b.μ volume * eLpNorm (k₁ - k₂) 2 volume
        < eLpNorm (k₁ - k₂) 2 volume := by
      calc eLpNormEssSup b.μ volume * eLpNorm (k₁ - k₂) 2 volume
          = eLpNorm (k₁ - k₂) 2 volume * eLpNormEssSup b.μ volume := mul_comm _ _
        _ < eLpNorm (k₁ - k₂) 2 volume * 1 :=
            ENNReal.mul_lt_mul_right h0 hfin b.bound
        _ = eLpNorm (k₁ - k₂) 2 volume := mul_one _
    exact absurd (lt_of_le_of_lt hnorm hlt) (lt_irrefl _)
  have hae : (k₁ - k₂ : ℂ → ℂ) =ᵐ[volume] 0 :=
    (eLpNorm_eq_zero_iff hδL2.1 (by norm_num)).mp hzero
  have hk₁₂ : k₁ =ᵐ[volume] k₂ := by
    filter_upwards [hae] with z hz
    have hz' : k₁ z - k₂ z = 0 := hz
    exact sub_eq_zero.mp hz'
  -- The Cauchy transforms agree, hence the solutions.
  funext z
  rw [hrepr₁ z, hrepr₂ z]
  congr 1
  rw [cauchyTransform, cauchyTransform]
  congr 1
  apply integral_congr_ae
  filter_upwards [hk₁₂] with ζ hζ
  rw [hζ]

end NoWanderingDomains
