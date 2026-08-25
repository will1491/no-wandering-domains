/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.Deformation.SphereVectorField.Basic

/-!
# Transport of the weak `∂̄`-class and the solver equation

The weak `∂̄`-derivative class with `L²_loc` gradient transports under the
inversion chart, and the canonical solver solves `∂̄(dbarSolver μ) = μ` weakly
on the finite chart.

* `hasL2WeakDzbar_inversion_transport` — the inversion transport.
* `hasL2WeakDzbar_dbarSolver` — the solver equation.
-/

open MeasureTheory Complex Metric Filter Topology
open scoped ENNReal NNReal ContDiff

namespace NoWanderingDomains

set_option maxHeartbeats 400000 in
-- The chart-transport `∂̄` lemma elaborates as one large declaration whose nested
-- weak-derivative and `L²_loc` `have` chains exceed the default heartbeat budget.
/-- **Chart transport of weak `∂̄`-data under the inversion `z ↦ 1/z`.**
Let `Ω ⊆ ℂ ∖ {0}` be open and let `u` be continuous with weak `∂̄`-derivative
`ν` (and `L²_loc` gradient) on the inverted set `(·⁻¹) '' Ω`. Then the
transported vector field `z ↦ −z²·u(1/z)` has weak `∂̄`-derivative
`(z²/z̄²)·ν(1/z)` on `Ω` — the Beltrami transformation law at the level of
weak derivatives:

`∂̄(−z²·u(1/z)) = (z²/z̄²)·(∂̄u)(1/z)` a.e. on `Ω`.

The `L²_loc` class is preserved because the Dirichlet integral is conformally
invariant under the (holomorphic) inversion. This is the analytic core of the
far-piece bookkeeping in `dbarSolver`, stated as a reusable node: mollify `u`
in the inverted chart, transport the classical chain rule, and pass to the
limit against test functions supported in `Ω`. -/
theorem hasL2WeakDzbar_inversion_transport {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hΩ0 : Ω ⊆ {(0 : ℂ)}ᶜ) {u ν : ℂ → ℂ}
    (hu : ContinuousOn u ((fun z : ℂ => z⁻¹) '' Ω))
    (hgrad : HasL2WeakDzbar u ν ((fun z : ℂ => z⁻¹) '' Ω)) :
    HasL2WeakDzbar (fun z => -z ^ 2 * u z⁻¹)
      (fun z => z ^ 2 / (starRingEnd ℂ z) ^ 2 * ν z⁻¹) Ω := by
  classical
  have : IsScalarTower ℝ ℂ ℂ := IsScalarTower.right
  obtain ⟨Gx, Gy, ⟨hGx, hGy⟩, hGx2, hGy2, haeQ⟩ := hgrad
  set Ω' : Set ℂ := (fun z : ℂ => z⁻¹) '' Ω with hΩ'def
  -- the `dz`- and `dzbar`-parts of the weak gradient of `u`
  set P : ℂ → ℂ := fun w => (2⁻¹ : ℂ) * (Gx w - Complex.I * Gy w) with hPdef
  set Q : ℂ → ℂ := fun w => (2⁻¹ : ℂ) * (Gx w + Complex.I * Gy w) with hQdef
  -- the transported `dz`- and `dzbar`-derivatives of `v(z) = -z²·u(1/z)`
  set A : ℂ → ℂ := fun z => -(2 * (z * u z⁻¹)) + P z⁻¹ with hAdef
  set B : ℂ → ℂ := fun z => z ^ 2 / (starRingEnd ℂ z) ^ 2 * Q z⁻¹ with hBdef
  /- ### Geometry of the inversion -/
  have hmemimg : ∀ (S : Set ℂ) (z : ℂ), z ∈ (fun w : ℂ => w⁻¹) '' S ↔ z⁻¹ ∈ S := by
    intro S z
    constructor
    · rintro ⟨w, hw, rfl⟩; rwa [inv_inv]
    · intro h; exact ⟨z⁻¹, h, inv_inv z⟩
  have hΩ0' : ∀ z ∈ Ω, z ≠ 0 := fun z hz => hΩ0 hz
  have hΩ'0 : ∀ w ∈ Ω', w ≠ 0 := by
    rintro w ⟨w₀, hw₀, rfl⟩
    exact inv_ne_zero (hΩ0' w₀ hw₀)
  have hΩ'open : IsOpen Ω' := by
    have hset : Ω' = {(0 : ℂ)}ᶜ ∩ (fun z : ℂ => z⁻¹) ⁻¹' Ω := by
      ext z
      constructor
      · intro hz
        exact ⟨hΩ'0 z hz, (hmemimg Ω z).mp hz⟩
      · rintro ⟨_, hz⟩
        exact (hmemimg Ω z).mpr hz
    rw [hset]
    exact ContinuousOn.isOpen_inter_preimage continuousOn_inv₀ isOpen_compl_singleton hΩ
  have himg : (fun z : ℂ => z⁻¹) '' Ω' = Ω := by
    ext z
    rw [hmemimg Ω' z, hmemimg Ω z⁻¹, inv_inv]
  have hinvinvimg : ∀ T : Set ℂ, (fun w : ℂ => w⁻¹) '' ((fun w : ℂ => w⁻¹) '' T) = T := by
    intro T
    ext z
    rw [hmemimg _ z, hmemimg T z⁻¹, inv_inv]
  have hcompimg : ∀ K : Set ℂ, IsCompact K → (∀ x ∈ K, x ≠ 0) →
      IsCompact ((fun w : ℂ => w⁻¹) '' K) := by
    intro K hK h0
    exact hK.image_of_continuousOn (continuousOn_inv₀.mono (fun x hx => h0 x hx))
  have hbound : ∀ K : Set ℂ, IsCompact K → (∀ x ∈ K, x ≠ 0) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ ‖x‖ := by
    intro K hK h0
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, fun x hx => absurd hx (Set.notMem_empty x)⟩
    · obtain ⟨x₀, hx₀K, hx₀⟩ :=
        IsCompact.exists_isMinOn hK hne continuous_norm.continuousOn
      exact ⟨‖x₀‖, norm_pos_iff.mpr (h0 x₀ hx₀K), fun x hx => hx₀ hx⟩
  /- ### Wirtinger derivatives and Jacobian of the inversion -/
  have hdiffι : ∀ w : ℂ, w ≠ 0 → DifferentiableAt ℂ (fun z : ℂ => z⁻¹) w := by
    intro w hw
    exact differentiableAt_inv hw
  have hdiffιR : ∀ w : ℂ, w ≠ 0 → DifferentiableAt ℝ (fun z : ℂ => z⁻¹) w := by
    intro w hw
    exact (differentiableAt_complex_iff_differentiableAt_real.mp (hdiffι w hw)).1
  have hdzι : ∀ w : ℂ, w ≠ 0 → dz (fun z : ℂ => z⁻¹) w = -(w ^ 2)⁻¹ := by
    intro w hw
    rw [dz_eq_deriv_of_differentiableAt (hdiffι w hw)]
    exact (hasDerivAt_inv hw).deriv
  have hdzbarι : ∀ w : ℂ, w ≠ 0 → dzbar (fun z : ℂ => z⁻¹) w = 0 := by
    intro w hw
    exact dzbar_eq_zero_of_differentiableAt (hdiffι w hw)
  have hdet : ∀ w : ℂ, w ≠ 0 →
      (fderiv ℝ (fun z : ℂ => z⁻¹) w).det = (‖w‖ ^ 4)⁻¹ := by
    intro w hw
    rw [det_fderiv_eq_wirtinger, hdzι w hw, hdzbarι w hw, norm_neg, norm_inv,
      norm_pow, norm_zero]
    ring
  have hfder : ∀ (S : Set ℂ), (∀ x ∈ S, x ≠ 0) → ∀ x ∈ S,
      HasFDerivWithinAt (fun w : ℂ => w⁻¹) (fderiv ℝ (fun w : ℂ => w⁻¹) x) S x := by
    intro S hS0 x hx
    exact ((hdiffιR x (hS0 x hx)).hasFDerivAt).hasFDerivWithinAt
  have hcovInt : ∀ S : Set ℂ, MeasurableSet S → (∀ x ∈ S, x ≠ 0) → ∀ F : ℂ → ℂ,
      ∫ z in (fun w : ℂ => w⁻¹) '' S, F z = ∫ w in S, ((‖w‖ ^ 4)⁻¹ : ℝ) • F w⁻¹ := by
    intro S hS hS0 F
    rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume hS
      (hfder S hS0) (inv_injective.injOn) F]
    refine setIntegral_congr_fun hS (fun w hw => ?_)
    rw [hdet w (hS0 w hw), abs_of_nonneg (by positivity)]
  have hcovLint : ∀ S : Set ℂ, MeasurableSet S → (∀ x ∈ S, x ≠ 0) → ∀ F : ℂ → ℝ≥0∞,
      ∫⁻ z in (fun w : ℂ => w⁻¹) '' S, F z
        = ∫⁻ w in S, ENNReal.ofReal ((‖w‖ ^ 4)⁻¹) * F w⁻¹ := by
    intro S hS hS0 F
    rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
      (hfder S hS0) (inv_injective.injOn) F]
    refine setLIntegral_congr_fun hS (fun w hw => ?_)
    rw [hdet w (hS0 w hw), abs_of_nonneg (by positivity)]
  have hnullimg : ∀ N : Set ℂ, (∀ x ∈ N, x ≠ 0) → volume N = 0 →
      volume ((fun w : ℂ => w⁻¹) '' N) = 0 := by
    intro N h0 hN
    refine MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      volume (fun x hx => ?_) hN
    exact (hdiffιR x (h0 x hx)).differentiableWithinAt
  have haetransSet : ∀ S : Set ℂ, (∀ x ∈ S, x ≠ 0) → ∀ p : ℂ → Prop,
      (∀ᵐ w ∂(volume : Measure ℂ), w ∈ S → p w) →
      (∀ᵐ z ∂(volume : Measure ℂ), z ∈ (fun w : ℂ => w⁻¹) '' S → p z⁻¹) := by
    intro S hS0 p hp
    rw [ae_iff] at hp ⊢
    have hbadnull : volume {w : ℂ | w ∈ S ∧ ¬ p w} = 0 := by
      refine measure_mono_null (fun w hw => ?_) hp
      simp only [Set.mem_ofPred_eq] at hw ⊢
      exact fun h => hw.2 (h hw.1)
    refine measure_mono_null (fun z hz => ?_)
      (hnullimg {w : ℂ | w ∈ S ∧ ¬ p w} (fun x hx => hS0 x hx.1) hbadnull)
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hz
    exact ⟨z⁻¹, ⟨(hmemimg S z).mp hz.1, hz.2⟩, inv_inv z⟩
  /- ### Integrability classes -/
  have huloc : LocallyIntegrableOn u Ω' :=
    hu.locallyIntegrableOn hΩ'open.measurableSet
  have hMemLoc : ∀ S : Set ℂ, IsOpen S → ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 S →
      LocallyIntegrableOn g S := by
    intro S hSopen g hg
    rw [MeasureTheory.locallyIntegrableOn_iff hSopen.isLocallyClosed]
    intro k hkS hk
    have : IsFiniteMeasure ((volume : Measure ℂ).restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact (hg k hkS hk).integrable (by norm_num)
  have hP2 : MemLpLocOn P 2 Ω' := by
    intro K hK hKc
    exact MemLp.const_mul
      ((hGx2 K hK hKc).sub ((hGy2 K hK hKc).const_mul Complex.I)) 2⁻¹
  have hQ2 : MemLpLocOn Q 2 Ω' := by
    intro K hK hKc
    exact MemLp.const_mul
      ((hGx2 K hK hKc).add ((hGy2 K hK hKc).const_mul Complex.I)) 2⁻¹
  have hPloc : LocallyIntegrableOn P Ω' := hMemLoc Ω' hΩ'open hP2
  have hQloc : LocallyIntegrableOn Q Ω' := hMemLoc Ω' hΩ'open hQ2
  have hGxloc : LocallyIntegrableOn Gx Ω' := hMemLoc Ω' hΩ'open hGx2
  have hGyloc : LocallyIntegrableOn Gy Ω' := hMemLoc Ω' hΩ'open hGy2
  have hmaps : ∀ z ∈ Ω, z⁻¹ ∈ Ω' := fun z hz => ⟨z, hz, rfl⟩
  have hinvcontΩ : ContinuousOn (fun z : ℂ => z⁻¹) Ω :=
    continuousOn_inv₀.mono (fun z hz => hΩ0' z hz)
  have hVcont : ContinuousOn (fun z : ℂ => -z ^ 2 * u z⁻¹) Ω := by
    refine ContinuousOn.mul ?_ (hu.comp hinvcontΩ hmaps)
    exact ((continuous_pow 2).continuousOn).neg
  have hVloc : LocallyIntegrableOn (fun z : ℂ => -z ^ 2 * u z⁻¹) Ω :=
    hVcont.locallyIntegrableOn hΩ.measurableSet
  /- ### `L²_loc` transport through the inversion -/
  have hL2inv : ∀ h : ℂ → ℂ, MemLpLocOn h 2 Ω' → MemLpLocOn (fun z => h z⁻¹) 2 Ω := by
    intro h hh K hKΩ hKc
    have hK0 : ∀ x ∈ K, x ≠ 0 := fun x hx => hΩ0' x (hKΩ hx)
    have hKmeas : MeasurableSet K := hKc.measurableSet
    set K' : Set ℂ := (fun w : ℂ => w⁻¹) '' K with hK'def
    have hK'c : IsCompact K' := hcompimg K hKc hK0
    have hK'0 : ∀ x ∈ K', x ≠ 0 := by
      rintro x ⟨y, hy, rfl⟩; exact inv_ne_zero (hK0 y hy)
    have hK'meas : MeasurableSet K' := hK'c.measurableSet
    have hK'Ω' : K' ⊆ Ω' := by
      rw [hK'def, hΩ'def]; exact Set.image_mono hKΩ
    have hKimg : (fun w : ℂ => w⁻¹) '' K' = K := hinvinvimg K
    have hmem : MemLp h 2 (volume.restrict K') := hh K' hK'Ω' hK'c
    constructor
    · -- a.e. strong measurability of `h ∘ ι` on `K`
      obtain ⟨h', h'meas, h'ae⟩ := hmem.aestronglyMeasurable
      refine ⟨fun z => h' z⁻¹, h'meas.comp_measurable measurable_inv, ?_⟩
      have hglob : ∀ᵐ w ∂(volume : Measure ℂ), w ∈ K' → h w = h' w :=
        (ae_restrict_iff' hK'meas).mp h'ae
      have htrans := haetransSet K' hK'0 (fun w => h w = h' w) hglob
      rw [hKimg] at htrans
      rw [Filter.EventuallyEq, ae_restrict_iff' hKmeas]
      filter_upwards [htrans] with z hz hzK
      exact hz hzK
    · -- finiteness of the transported `L²` norm
      have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
      have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne0 h2netop]
      refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
      obtain ⟨δ, hδpos, hδ⟩ := hbound K' hK'c hK'0
      have hcov := hcovLint K' hK'meas hK'0
        (fun z => ‖h z⁻¹‖ₑ ^ (2 : ℝ≥0∞).toReal)
      rw [hKimg] at hcov
      have hlt : ∫⁻ w in K', ‖h w‖ₑ ^ (2 : ℝ≥0∞).toReal < ⊤ := by
        have := hmem.2
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne0 h2netop] at this
        exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp this
      have hmono : ∫⁻ w in K',
          ENNReal.ofReal ((‖w‖ ^ 4)⁻¹) * ‖h (w⁻¹)⁻¹‖ₑ ^ (2 : ℝ≥0∞).toReal
          ≤ ∫⁻ w in K', ENNReal.ofReal ((δ ^ 4)⁻¹) * ‖h w‖ₑ ^ (2 : ℝ≥0∞).toReal := by
        refine lintegral_mono_ae ?_
        rw [ae_restrict_iff' hK'meas]
        refine ae_of_all _ (fun w hw => ?_)
        rw [inv_inv]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        refine inv_anti₀ (by positivity) ?_
        exact pow_le_pow_left₀ hδpos.le (hδ w hw) 4
      have hfin : ∫⁻ z in K, ‖h z⁻¹‖ₑ ^ (2 : ℝ≥0∞).toReal < ⊤ :=
        calc ∫⁻ z in K, ‖h z⁻¹‖ₑ ^ (2 : ℝ≥0∞).toReal
            = ∫⁻ w in K', ENNReal.ofReal ((‖w‖ ^ 4)⁻¹)
                * ‖h (w⁻¹)⁻¹‖ₑ ^ (2 : ℝ≥0∞).toReal := hcov
          _ ≤ ∫⁻ w in K', ENNReal.ofReal ((δ ^ 4)⁻¹)
                * ‖h w‖ₑ ^ (2 : ℝ≥0∞).toReal := hmono
          _ = ENNReal.ofReal ((δ ^ 4)⁻¹)
                * ∫⁻ w in K', ‖h w‖ₑ ^ (2 : ℝ≥0∞).toReal :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlt
      exact hfin.ne
  /- ### `L²_loc` of the transported Wirtinger parts -/
  have hA2 : MemLpLocOn A 2 Ω := by
    intro K hKΩ hKc
    have : IsFiniteMeasure ((volume : Measure ℂ).restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    have hcont1 : ContinuousOn (fun z : ℂ => -(2 * (z * u z⁻¹))) Ω :=
      (continuousOn_const.mul (continuousOn_id.mul (hu.comp hinvcontΩ hmaps))).neg
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hcont1.mono hKΩ)
    have h1 : MemLp (fun z : ℂ => -(2 * (z * u z⁻¹))) 2 (volume.restrict K) := by
      refine MemLp.of_bound
        ((hcont1.mono hKΩ).aestronglyMeasurable hKc.measurableSet) C ?_
      rw [ae_restrict_iff' hKc.measurableSet]
      exact ae_of_all _ hC
    exact h1.add (hL2inv P hP2 K hKΩ hKc)
  have hB2 : MemLpLocOn B 2 Ω := by
    intro K hKΩ hKc
    have hq := hL2inv Q hQ2 K hKΩ hKc
    have hK0 : ∀ x ∈ K, x ≠ 0 := fun x hx => hΩ0' x (hKΩ hx)
    have hfrac : ContinuousOn (fun z : ℂ => z ^ 2 / (starRingEnd ℂ z) ^ 2) K := by
      refine ContinuousOn.div (continuous_pow 2).continuousOn
        (((continuous_conj).pow 2).continuousOn) ?_
      intro x hx
      exact pow_ne_zero 2 ((starRingEnd_apply x ▸ star_ne_zero.mpr (hK0 x hx)))
    refine MemLp.of_le hq
      ((hfrac.aestronglyMeasurable hKc.measurableSet).mul hq.aestronglyMeasurable) ?_
    refine ae_of_all _ (fun z => ?_)
    rw [hBdef]
    simp only [norm_mul, norm_div, norm_pow, Complex.norm_conj]
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    · rw [div_self (by positivity)]
      simp
  /- ### Integrability of (test)·(locally integrable) products -/
  have integC : ∀ m : ℂ → ℂ, Continuous m → HasCompactSupport m →
      ∀ {S : Set ℂ}, tsupport m ⊆ S → ∀ {h : ℂ → ℂ}, LocallyIntegrableOn h S →
      Integrable (fun z => m z * h z) volume := by
    intro m hm hcsm S htsm h hh
    have hK : IsCompact (tsupport m) := hcsm
    have hhon : IntegrableOn h (tsupport m) volume :=
      hh.integrableOn_compact_subset htsm hK
    have hon : IntegrableOn (fun z => m z * h z) (tsupport m) volume := by
      have := hhon.continuousOn_smul hm.continuousOn hK
      simpa only [smul_eq_mul] using this
    have hsupp : Function.support (fun z => m z * h z) ⊆ tsupport m := by
      intro z hz
      apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  /- ### The complexified directional pairing -/
  have hUC : ∀ (v₀ : ℂ) (G : ℂ → ℂ), HasWeakDirDeriv v₀ G u Ω' →
      LocallyIntegrableOn G Ω' →
      ∀ Ψ : ℂ → ℂ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Ω' →
      ∫ w, (fderiv ℝ Ψ w) v₀ * u w = -∫ w, Ψ w * G w := by
    intro v₀ G hG hGloc Ψ hΨ hΨcs hΨts
    have hts_of : ∀ g : ℂ → ℝ, (∀ w, Ψ w = 0 → g w = 0) → tsupport g ⊆ tsupport Ψ := by
      intro g hg
      refine closure_minimal (fun w hw => subset_tsupport Ψ ?_) (isClosed_tsupport Ψ)
      intro h0
      exact hw (hg w h0)
    set ψ₁ : ℂ → ℝ := fun w => (Ψ w).re with hψ₁def
    set ψ₂ : ℂ → ℝ := fun w => (Ψ w).im with hψ₂def
    have hψ₁c : ContDiff ℝ ∞ ψ₁ := Complex.reCLM.contDiff.comp hΨ
    have hψ₂c : ContDiff ℝ ∞ ψ₂ := Complex.imCLM.contDiff.comp hΨ
    have hψ₁ts : tsupport ψ₁ ⊆ tsupport Ψ := hts_of ψ₁ (fun w h0 => by simp [hψ₁def, h0])
    have hψ₂ts : tsupport ψ₂ ⊆ tsupport Ψ := hts_of ψ₂ (fun w h0 => by simp [hψ₂def, h0])
    have hψ₁cs : HasCompactSupport ψ₁ :=
      IsCompact.of_isClosed_subset hΨcs (isClosed_tsupport ψ₁) hψ₁ts
    have hψ₂cs : HasCompactSupport ψ₂ :=
      IsCompact.of_isClosed_subset hΨcs (isClosed_tsupport ψ₂) hψ₂ts
    have hΨdiff : ∀ w, DifferentiableAt ℝ Ψ w :=
      fun w => (hΨ.differentiable (by norm_num)).differentiableAt
    have hfd : ∀ w : ℂ, (fderiv ℝ Ψ w) v₀
        = ((fderiv ℝ ψ₁ w) v₀ : ℂ) + ((fderiv ℝ ψ₂ w) v₀ : ℂ) * Complex.I := by
      intro w
      have h₁ : fderiv ℝ ψ₁ w = Complex.reCLM.comp (fderiv ℝ Ψ w) :=
        (Complex.reCLM.hasFDerivAt.comp w (hΨdiff w).hasFDerivAt).fderiv
      have h₂ : fderiv ℝ ψ₂ w = Complex.imCLM.comp (fderiv ℝ Ψ w) :=
        (Complex.imCLM.hasFDerivAt.comp w (hΨdiff w).hasFDerivAt).fderiv
      rw [h₁, h₂]
      simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
      exact (Complex.re_add_im _).symm
    -- continuity / support of the directional-derivative multipliers
    have hcont₁ : Continuous (fun w => ((fderiv ℝ ψ₁ w) v₀ : ℝ)) :=
      (hψ₁c.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcont₂ : Continuous (fun w => ((fderiv ℝ ψ₂ w) v₀ : ℝ)) :=
      (hψ₂c.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs₁ : HasCompactSupport (fun w => ((fderiv ℝ ψ₁ w) v₀ : ℝ)) :=
      HasCompactSupport.fderiv_apply ℝ hψ₁cs v₀
    have hcs₂ : HasCompactSupport (fun w => ((fderiv ℝ ψ₂ w) v₀ : ℝ)) :=
      HasCompactSupport.fderiv_apply ℝ hψ₂cs v₀
    have hts₁ : tsupport (fun w => ((fderiv ℝ ψ₁ w) v₀ : ℝ)) ⊆ Ω' :=
      ((tsupport_fderiv_apply_subset ℝ v₀).trans hψ₁ts).trans hΨts
    have hts₂ : tsupport (fun w => ((fderiv ℝ ψ₂ w) v₀ : ℝ)) ⊆ Ω' :=
      ((tsupport_fderiv_apply_subset ℝ v₀).trans hψ₂ts).trans hΨts
    -- casting a real multiplier to `ℂ` preserves the test-function properties
    have hcastC : ∀ g : ℂ → ℝ, Continuous g → Continuous (fun w => ((g w : ℝ) : ℂ)) :=
      fun g hg => Complex.continuous_ofReal.comp hg
    have hcastCS : ∀ g : ℂ → ℝ, HasCompactSupport g →
        HasCompactSupport (fun w => ((g w : ℝ) : ℂ)) :=
      fun g hg => hg.comp_left Complex.ofReal_zero
    have hcastTS : ∀ g : ℂ → ℝ, tsupport (fun w => ((g w : ℝ) : ℂ)) ⊆ tsupport g := by
      intro g
      refine closure_minimal (fun w hw => subset_tsupport g ?_) (isClosed_tsupport g)
      simp only [Function.mem_support] at hw ⊢
      intro h0; apply hw; simp [h0]
    -- the four integrable pieces
    have hi₁ : Integrable (fun w => (((fderiv ℝ ψ₁ w) v₀ : ℝ) : ℂ) * u w) volume :=
      integC _ (hcastC _ hcont₁) (hcastCS _ hcs₁) ((hcastTS _).trans hts₁) huloc
    have hi₂ : Integrable (fun w => (((fderiv ℝ ψ₂ w) v₀ : ℝ) : ℂ)
        * (Complex.I * u w)) volume := by
      have base : Integrable
          (fun w => (Complex.I * (((fderiv ℝ ψ₂ w) v₀ : ℝ) : ℂ)) * u w) volume :=
        integC _ (continuous_const.mul (hcastC _ hcont₂))
          ((hcastCS _ hcs₂).mul_left)
          (tsupport_mul_subset_right.trans ((hcastTS _).trans hts₂)) huloc
      refine base.congr (ae_of_all _ (fun w => ?_))
      ring
    have hi₃ : Integrable (fun w => ((ψ₁ w : ℝ) : ℂ) * G w) volume :=
      integC _ (hcastC _ hψ₁c.continuous) (hcastCS _ hψ₁cs)
        ((hcastTS _).trans (hψ₁ts.trans hΨts)) hGloc
    have hi₄ : Integrable (fun w => ((ψ₂ w : ℝ) : ℂ) * (Complex.I * G w)) volume := by
      have base : Integrable
          (fun w => (Complex.I * ((ψ₂ w : ℝ) : ℂ)) * G w) volume :=
        integC _ (continuous_const.mul (hcastC _ hψ₂c.continuous))
          ((hcastCS _ hψ₂cs).mul_left)
          (tsupport_mul_subset_right.trans ((hcastTS _).trans (hψ₂ts.trans hΨts))) hGloc
      refine base.congr (ae_of_all _ (fun w => ?_))
      ring
    -- the two real tested identities, in `ℂ`-multiplication form
    have e₁ := hG ψ₁ hψ₁c hψ₁cs (hψ₁ts.trans hΨts)
    have hGI' : HasWeakDirDeriv v₀ (fun z => Complex.I • G z)
        (fun z => Complex.I • u z) Ω' := hG.const_smul Complex.I
    have e₂ := hGI' ψ₂ hψ₂c hψ₂cs (hψ₂ts.trans hΨts)
    simp only [Complex.real_smul, smul_eq_mul] at e₁ e₂
    -- assemble
    calc ∫ w, (fderiv ℝ Ψ w) v₀ * u w
        = ∫ w, ((((fderiv ℝ ψ₁ w) v₀ : ℝ) : ℂ) * u w
            + (((fderiv ℝ ψ₂ w) v₀ : ℝ) : ℂ) * (Complex.I * u w)) := by
          refine integral_congr_ae (ae_of_all _ (fun w => ?_))
          simp only
          rw [hfd w]; ring
      _ = (∫ w, (((fderiv ℝ ψ₁ w) v₀ : ℝ) : ℂ) * u w)
            + ∫ w, (((fderiv ℝ ψ₂ w) v₀ : ℝ) : ℂ) * (Complex.I * u w) :=
          integral_add hi₁ hi₂
      _ = (-∫ w, ((ψ₁ w : ℝ) : ℂ) * G w)
            + -∫ w, ((ψ₂ w : ℝ) : ℂ) * (Complex.I * G w) := by rw [e₁, e₂]
      _ = -((∫ w, ((ψ₁ w : ℝ) : ℂ) * G w)
            + ∫ w, ((ψ₂ w : ℝ) : ℂ) * (Complex.I * G w)) := (neg_add _ _).symm
      _ = -∫ w, (((ψ₁ w : ℝ) : ℂ) * G w + ((ψ₂ w : ℝ) : ℂ) * (Complex.I * G w)) := by
          rw [integral_add hi₃ hi₄]
      _ = -∫ w, Ψ w * G w := by
          rw [neg_inj]
          refine integral_congr_ae (ae_of_all _ (fun w => ?_))
          simp only [hψ₁def, hψ₂def]
          linear_combination (Complex.re_add_im (Ψ w)) * G w
  /- ### Wirtinger-form pairings on the inverted chart -/
  have hfdtest : ∀ Ψ : ℂ → ℂ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Ω' →
      ∀ v₀ : ℂ, Integrable (fun w => (fderiv ℝ Ψ w) v₀ * u w) volume := by
    intro Ψ hΨ hΨcs hΨts v₀
    refine integC _ ?_ ?_ ?_ huloc
    · exact (hΨ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    · exact HasCompactSupport.fderiv_apply ℝ hΨcs v₀
    · exact (tsupport_fderiv_apply_subset ℝ v₀).trans hΨts
  have hpull : ∀ (c d : ℂ) (f : ℂ → ℂ), ∫ w, c * (d * f w) = c * (d * ∫ w, f w) := by
    intro c d f
    calc ∫ w, c * (d * f w)
        = ∫ w, (c * d) * f w := integral_congr_ae (ae_of_all _ (fun w => by ring))
      _ = (c * d) * ∫ w, f w := integral_const_mul _ _
      _ = c * (d * ∫ w, f w) := by ring
  have hU1 : ∀ Ψ : ℂ → ℂ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Ω' →
      ∫ w, dz Ψ w * u w = -∫ w, Ψ w * P w := by
    intro Ψ hΨ hΨcs hΨts
    have hx := hUC 1 Gx hGx hGxloc Ψ hΨ hΨcs hΨts
    have hy := hUC Complex.I Gy hGy hGyloc Ψ hΨ hΨcs hΨts
    have hi₁ := hfdtest Ψ hΨ hΨcs hΨts 1
    have hi₂ := hfdtest Ψ hΨ hΨcs hΨts Complex.I
    have hg₁ : Integrable (fun w => Ψ w * Gx w) volume :=
      integC _ hΨ.continuous hΨcs hΨts hGxloc
    have hg₂ : Integrable (fun w => Ψ w * Gy w) volume :=
      integC _ hΨ.continuous hΨcs hΨts hGyloc
    calc ∫ w, dz Ψ w * u w
        = ∫ w, ((2⁻¹ : ℂ) * ((fderiv ℝ Ψ w) 1 * u w)
            - (2⁻¹ : ℂ) * (Complex.I * ((fderiv ℝ Ψ w) Complex.I * u w))) := by
          refine integral_congr_ae (ae_of_all _ (fun w => ?_))
          simp only [dz]
          ring
      _ = (2⁻¹ : ℂ) * (∫ w, (fderiv ℝ Ψ w) 1 * u w)
            - (2⁻¹ : ℂ) * (Complex.I * ∫ w, (fderiv ℝ Ψ w) Complex.I * u w) := by
          rw [integral_sub (hi₁.const_mul _) ((hi₂.const_mul Complex.I).const_mul _)]
          congr 1
          · exact integral_const_mul _ _
          · exact hpull _ _ _
      _ = (2⁻¹ : ℂ) * (-∫ w, Ψ w * Gx w)
            - (2⁻¹ : ℂ) * (Complex.I * -∫ w, Ψ w * Gy w) := by rw [hx, hy]
      _ = -((2⁻¹ : ℂ) * (∫ w, Ψ w * Gx w)
            - (2⁻¹ : ℂ) * (Complex.I * ∫ w, Ψ w * Gy w)) := by ring
      _ = -∫ w, ((2⁻¹ : ℂ) * (Ψ w * Gx w)
            - (2⁻¹ : ℂ) * (Complex.I * (Ψ w * Gy w))) := by
          rw [neg_inj, integral_sub (hg₁.const_mul _) ((hg₂.const_mul Complex.I).const_mul _)]
          congr 1
          · exact (integral_const_mul _ _).symm
          · exact (hpull _ _ _).symm
      _ = -∫ w, Ψ w * P w := by
          rw [neg_inj]
          refine integral_congr_ae (ae_of_all _ (fun w => ?_))
          simp only [hPdef]
          ring
  have hU2 : ∀ Ψ : ℂ → ℂ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Ω' →
      ∫ w, dzbar Ψ w * u w = -∫ w, Ψ w * Q w := by
    intro Ψ hΨ hΨcs hΨts
    have hx := hUC 1 Gx hGx hGxloc Ψ hΨ hΨcs hΨts
    have hy := hUC Complex.I Gy hGy hGyloc Ψ hΨ hΨcs hΨts
    have hi₁ := hfdtest Ψ hΨ hΨcs hΨts 1
    have hi₂ := hfdtest Ψ hΨ hΨcs hΨts Complex.I
    have hg₁ : Integrable (fun w => Ψ w * Gx w) volume :=
      integC _ hΨ.continuous hΨcs hΨts hGxloc
    have hg₂ : Integrable (fun w => Ψ w * Gy w) volume :=
      integC _ hΨ.continuous hΨcs hΨts hGyloc
    calc ∫ w, dzbar Ψ w * u w
        = ∫ w, ((2⁻¹ : ℂ) * ((fderiv ℝ Ψ w) 1 * u w)
            + (2⁻¹ : ℂ) * (Complex.I * ((fderiv ℝ Ψ w) Complex.I * u w))) := by
          refine integral_congr_ae (ae_of_all _ (fun w => ?_))
          simp only [dzbar]
          ring
      _ = (2⁻¹ : ℂ) * (∫ w, (fderiv ℝ Ψ w) 1 * u w)
            + (2⁻¹ : ℂ) * (Complex.I * ∫ w, (fderiv ℝ Ψ w) Complex.I * u w) := by
          rw [integral_add (hi₁.const_mul _) ((hi₂.const_mul Complex.I).const_mul _)]
          congr 1
          · exact integral_const_mul _ _
          · exact hpull _ _ _
      _ = (2⁻¹ : ℂ) * (-∫ w, Ψ w * Gx w)
            + (2⁻¹ : ℂ) * (Complex.I * -∫ w, Ψ w * Gy w) := by rw [hx, hy]
      _ = -((2⁻¹ : ℂ) * (∫ w, Ψ w * Gx w)
            + (2⁻¹ : ℂ) * (Complex.I * ∫ w, Ψ w * Gy w)) := by ring
      _ = -∫ w, ((2⁻¹ : ℂ) * (Ψ w * Gx w)
            + (2⁻¹ : ℂ) * (Complex.I * (Ψ w * Gy w))) := by
          rw [neg_inj, integral_add (hg₁.const_mul _) ((hg₂.const_mul Complex.I).const_mul _)]
          congr 1
          · exact (integral_const_mul _ _).symm
          · exact (hpull _ _ _).symm
      _ = -∫ w, Ψ w * Q w := by
          rw [neg_inj]
          refine integral_congr_ae (ae_of_all _ (fun w => ?_))
          simp only [hQdef]
          ring
  /- ### Change of variables specialised to `Ω`, and support vanishing -/
  have hcovΩ : ∀ F : ℂ → ℂ, ∫ z in Ω, F z = ∫ w in Ω', ((‖w‖ ^ 4)⁻¹ : ℝ) • F w⁻¹ := by
    intro F
    rw [← himg]
    exact hcovInt Ω' hΩ'open.measurableSet hΩ'0 F
  have hfd0 : ∀ (Ψ : ℂ → ℂ) (z : ℂ), z ∉ tsupport Ψ → dz Ψ z = 0 ∧ dzbar Ψ z = 0 := by
    intro Ψ z hz
    have h0 : fderiv ℝ Ψ z = 0 := by
      by_contra hne
      exact hz (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
    constructor <;> simp [dz, dzbar, h0]
  have hdzsupp : ∀ Ψ : ℂ → ℂ, tsupport (fun z => dz Ψ z) ⊆ tsupport Ψ ∧
      tsupport (fun z => dzbar Ψ z) ⊆ tsupport Ψ := by
    intro Ψ
    constructor <;>
    · refine closure_minimal (fun z hz => ?_) (isClosed_tsupport Ψ)
      by_contra hnot
      simp only [Function.mem_support] at hz
      first
        | exact hz (hfd0 Ψ z hnot).1
        | exact hz (hfd0 Ψ z hnot).2
  have hAloc : LocallyIntegrableOn A Ω := hMemLoc Ω hΩ hA2
  have hBloc : LocallyIntegrableOn B Ω := hMemLoc Ω hΩ hB2
  /- ### Smoothness of the inversion-side multipliers -/
  have hinvCD : ∀ w : ℂ, w ≠ 0 → ContDiffAt ℝ ∞ (fun z : ℂ => z⁻¹) w := by
    intro w hw
    exact contDiffAt_id.inv hw
  have hcd_pow_inv : ∀ n : ℕ, ∀ w : ℂ, w ≠ 0 →
      ContDiffAt ℝ ∞ (fun z : ℂ => (z ^ n)⁻¹) w := by
    intro n w hw
    exact (contDiffAt_id.pow n).inv (pow_ne_zero n hw)
  have hcd_conj : ContDiff ℝ ∞ (fun z : ℂ => (starRingEnd ℂ) z) :=
    Complex.conjCLE.contDiff
  have hcd_conj_sq_inv : ∀ w : ℂ, w ≠ 0 →
      ContDiffAt ℝ ∞ (fun z : ℂ => ((starRingEnd ℂ z) ^ 2)⁻¹) w := by
    intro w hw
    refine ContDiffAt.inv (hcd_conj.contDiffAt.pow 2) ?_
    exact pow_ne_zero 2 (by rw [starRingEnd_apply]; exact star_ne_zero.mpr hw)
  have hcd_c3 : ∀ w : ℂ, w ≠ 0 →
      ContDiffAt ℝ ∞ (fun z : ℂ => -(2 * z ^ 1) * (((z ^ 2) ^ 2)⁻¹)) w := by
    intro w hw
    have h1 : ContDiffAt ℝ ∞ (fun z : ℂ => -(2 * z ^ 1)) w :=
      (contDiffAt_const.mul (contDiffAt_id.pow 1)).neg
    have h2 : ContDiffAt ℝ ∞ (fun z : ℂ => (((z ^ 2) ^ 2)⁻¹)) w :=
      ((contDiffAt_id.pow 2).pow 2).inv (pow_ne_zero 2 (pow_ne_zero 2 hw))
    exact h1.mul h2
  have hcontdz : ∀ Ψ : ℂ → ℂ, ContDiff ℝ ∞ Ψ →
      Continuous (fun z => dz Ψ z) ∧ Continuous (fun z => dzbar Ψ z) := by
    intro Ψ hΨ
    have h1 : Continuous (fun z => (fderiv ℝ Ψ z) 1) :=
      (hΨ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have h2 : Continuous (fun z => (fderiv ℝ Ψ z) Complex.I) :=
      (hΨ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    constructor
    · simp only [dz]
      exact continuous_const.mul (h1.sub (continuous_const.mul h2))
    · simp only [dzbar]
      exact continuous_const.mul (h1.add (continuous_const.mul h2))
  /- ### The Jacobian factor as a complex multiplier -/
  have hcast : ∀ w : ℂ,
      (((‖w‖ ^ 4)⁻¹ : ℝ) : ℂ) = (w ^ 2 * (starRingEnd ℂ w) ^ 2)⁻¹ := by
    intro w
    rw [Complex.ofReal_inv]
    congr 1
    have h1 : (w * (starRingEnd ℂ) w) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq w
    calc ((‖w‖ ^ 4 : ℝ) : ℂ) = (((‖w‖ ^ 2 : ℝ) : ℂ)) ^ 2 := by push_cast; ring
      _ = (w * (starRingEnd ℂ) w) ^ 2 := by rw [h1]
      _ = w ^ 2 * (starRingEnd ℂ w) ^ 2 := by ring
  /- ### The transported Wirtinger identities for the vector field -/
  have hW : ∀ Φ : ℂ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ → tsupport Φ ⊆ Ω →
      (∫ z, dz Φ z * (-z ^ 2 * u z⁻¹) = -∫ z, Φ z * A z) ∧
      (∫ z, dzbar Φ z * (-z ^ 2 * u z⁻¹) = -∫ z, Φ z * B z) := by
    intro Φ hΦ hΦcs hΦts
    have hΦdiff : ∀ z, DifferentiableAt ℝ Φ z :=
      fun z => (hΦ.differentiable (by norm_num)).differentiableAt
    -- the transported test function `χ = Φ ∘ ι`
    set χ : ℂ → ℂ := fun w => Φ w⁻¹ with hχdef
    set KΦ : Set ℂ := (fun w : ℂ => w⁻¹) '' (tsupport Φ) with hKΦdef
    have hΦts0 : ∀ x ∈ tsupport Φ, x ≠ 0 := fun x hx => hΩ0' x (hΦts hx)
    have hKΦc : IsCompact KΦ := hcompimg _ hΦcs hΦts0
    have hχsupp : Function.support χ ⊆ KΦ := by
      intro w hw
      have : Φ w⁻¹ ≠ 0 := hw
      exact ⟨w⁻¹, subset_tsupport Φ this, inv_inv w⟩
    have h0KΦ : (0 : ℂ) ∉ KΦ := by
      rintro ⟨y, hy, h0⟩
      exact hΦts0 y hy (inv_eq_zero.mp h0)
    have hχ0nhds : ∀ᶠ w in 𝓝 (0 : ℂ), χ w = 0 := by
      have hmem : KΦᶜ ∈ 𝓝 (0 : ℂ) := hKΦc.isClosed.isOpen_compl.mem_nhds h0KΦ
      filter_upwards [hmem] with w hw
      by_contra h
      exact hw (hχsupp h)
    have hχsmooth : ContDiff ℝ ∞ χ := by
      rw [contDiff_iff_contDiffAt]
      intro w
      rcases eq_or_ne w 0 with rfl | hw
      · exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hχ0nhds
      · exact hΦ.contDiffAt.comp w (hinvCD w hw)
    have hχts : tsupport χ ⊆ KΦ := closure_minimal hχsupp hKΦc.isClosed
    have hχcs : HasCompactSupport χ :=
      IsCompact.of_isClosed_subset hKΦc (isClosed_tsupport χ) hχts
    have hKΦΩ' : KΦ ⊆ Ω' := by
      rw [hKΦdef, hΩ'def]
      exact Set.image_mono hΦts
    have hχdiff : ∀ w, DifferentiableAt ℝ χ w :=
      fun w => (hχsmooth.differentiable (by norm_num)).differentiableAt
    -- multiplying `χ` by a coefficient that is smooth away from `0`
    have hmk : ∀ c : ℂ → ℂ, (∀ w : ℂ, w ≠ 0 → ContDiffAt ℝ ∞ c w) →
        ContDiff ℝ ∞ (fun w => c w * χ w) ∧ HasCompactSupport (fun w => c w * χ w) ∧
        tsupport (fun w => c w * χ w) ⊆ Ω' := by
      intro c hc
      have hsupp : Function.support (fun w => c w * χ w) ⊆ tsupport χ := by
        intro w hw
        refine subset_tsupport χ ?_
        simp only [Function.mem_support] at hw ⊢
        intro h0
        exact hw (by rw [h0, mul_zero])
      have hts : tsupport (fun w => c w * χ w) ⊆ tsupport χ :=
        closure_minimal hsupp (isClosed_tsupport χ)
      refine ⟨?_, IsCompact.of_isClosed_subset hχcs (isClosed_tsupport _) hts,
        hts.trans (hχts.trans hKΦΩ')⟩
      rw [contDiff_iff_contDiffAt]
      intro w
      rcases eq_or_ne w 0 with rfl | hw
      · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [hχ0nhds] with w hw
        rw [hw, mul_zero]
      · exact (hc w hw).mul hχsmooth.contDiffAt
    -- the two modified test functions and the correction multiplier
    obtain ⟨hΘsm, hΘcs, hΘts⟩ := hmk (fun w => (w ^ 4)⁻¹) (hcd_pow_inv 4)
    obtain ⟨hΞsm, hΞcs, hΞts⟩ := hmk
      (fun w => ((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹)
      (fun w hw => (hcd_conj_sq_inv w hw).mul (hcd_pow_inv 2 w hw))
    obtain ⟨hΛsm, hΛcs, hΛts⟩ := hmk
      (fun w => ((starRingEnd ℂ w) ^ 2)⁻¹ * (-(2 * w ^ 1) * (((w ^ 2) ^ 2)⁻¹)))
      (fun w hw => (hcd_conj_sq_inv w hw).mul (hcd_c3 w hw))
    -- Wirtinger derivatives of `χ` through the chain rule
    have hχdz : ∀ w : ℂ, w ≠ 0 → dz χ w = dz Φ w⁻¹ * -(w ^ 2)⁻¹ := by
      intro w hw
      have h := dz_comp (f := fun z : ℂ => z⁻¹) (g := Φ) (z := w)
        (hdiffιR w hw) (hΦdiff w⁻¹)
      rw [hdzι w hw, hdzbarι w hw] at h
      simpa using h
    have hχdzbar : ∀ w : ℂ, w ≠ 0 →
        dzbar χ w = dzbar Φ w⁻¹ * -(((starRingEnd ℂ) w) ^ 2)⁻¹ := by
      intro w hw
      have h := dzbar_comp (f := fun z : ℂ => z⁻¹) (g := Φ) (z := w)
        (hdiffιR w hw) (hΦdiff w⁻¹)
      rw [hdzι w hw, hdzbarι w hw] at h
      simp only [mul_zero, zero_add, map_neg, map_inv₀, map_pow] at h
      simpa using h
    -- Wirtinger derivatives of the modified test functions
    have hΘdzbar : ∀ w : ℂ, w ≠ 0 →
        dzbar (fun w => (w ^ 4)⁻¹ * χ w) w = (w ^ 4)⁻¹ * dzbar χ w := by
      intro w hw
      have hf : DifferentiableAt ℝ (fun z : ℂ => (z ^ 4)⁻¹) w :=
        (hcd_pow_inv 4 w hw).differentiableAt (by norm_num)
      have h := dzbar_mul (f := fun z : ℂ => (z ^ 4)⁻¹) (g := χ) (z := w) hf (hχdiff w)
      have hzero : dzbar (fun z : ℂ => (z ^ 4)⁻¹) w = 0 :=
        dzbar_eq_zero_of_differentiableAt
          ((differentiableAt_id.pow 4).inv (pow_ne_zero 4 hw))
      rw [h, hzero, mul_zero, add_zero]
    have hΞdz : ∀ w : ℂ, w ≠ 0 →
        dz (fun w => ((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * χ w) w
          = ((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * dz χ w
            + χ w * (((starRingEnd ℂ w) ^ 2)⁻¹
              * (-(2 * w ^ 1) * (((w ^ 2) ^ 2)⁻¹))) := by
      intro w hw
      have hc1 : DifferentiableAt ℝ (fun z : ℂ => ((starRingEnd ℂ z) ^ 2)⁻¹) w :=
        (hcd_conj_sq_inv w hw).differentiableAt (by norm_num)
      have hc2 : DifferentiableAt ℝ (fun z : ℂ => (z ^ 2)⁻¹) w :=
        (hcd_pow_inv 2 w hw).differentiableAt (by norm_num)
      have h := dz_mul
        (f := fun z : ℂ => ((starRingEnd ℂ z) ^ 2)⁻¹ * (z ^ 2)⁻¹) (g := χ) (z := w)
        (hc1.mul hc2) (hχdiff w)
      have h2 := dz_mul (f := fun z : ℂ => ((starRingEnd ℂ z) ^ 2)⁻¹)
        (g := fun z : ℂ => (z ^ 2)⁻¹) (z := w) hc1 hc2
      have h3 : dz (fun z : ℂ => (z ^ 2)⁻¹) w = -(2 * w ^ 1) * (((w ^ 2) ^ 2)⁻¹) := by
        have hd : HasDerivAt (fun z : ℂ => (z ^ 2)⁻¹)
            (-(2 * w ^ 1) * (((w ^ 2) ^ 2)⁻¹)) w := by
          simpa [div_eq_mul_inv] using! (hasDerivAt_pow 2 w).fun_inv (pow_ne_zero 2 hw)
        rw [dz_eq_deriv_of_differentiableAt hd.differentiableAt, hd.deriv]
      have h4 : dz (fun z : ℂ => ((starRingEnd ℂ z) ^ 2)⁻¹) w = 0 := by
        have hrw : (fun z : ℂ => ((starRingEnd ℂ z) ^ 2)⁻¹)
            = fun z : ℂ => (starRingEnd ℂ) ((z ^ 2)⁻¹) := by
          funext z
          rw [map_inv₀, map_pow]
        have hz2 : dzbar (fun z : ℂ => (z ^ 2)⁻¹) w = 0 :=
          dzbar_eq_zero_of_differentiableAt
            ((differentiableAt_id.pow 2).inv (pow_ne_zero 2 hw))
        rw [hrw, dz_conj (fun z : ℂ => (z ^ 2)⁻¹) w, hz2, map_zero]
      rw [h, h2, h3, h4]
      ring
    -- change of variables sending a tested integral to the inverted chart
    have hcovFull : ∀ F : ℂ → ℂ, (∀ z, z ∉ tsupport Φ → F z = 0) →
        ∫ z, F z = ∫ w, ((‖w‖ ^ 4)⁻¹ : ℝ) • F w⁻¹ := by
      intro F hF
      calc ∫ z, F z
          = ∫ z in Ω, F z :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero
              (fun z hz => hF z (fun hmem => hz (hΦts hmem)))).symm
        _ = ∫ w in Ω', ((‖w‖ ^ 4)⁻¹ : ℝ) • F w⁻¹ := hcovΩ F
        _ = ∫ w, ((‖w‖ ^ 4)⁻¹ : ℝ) • F w⁻¹ := by
            refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => ?_)
            have hFw : F w⁻¹ = 0 := by
              refine hF _ (fun hmem => hw (hKΦΩ' ⟨w⁻¹, hmem, inv_inv w⟩))
            rw [hFw]
            simp
    have h0Ω' : (0 : ℂ) ∉ Ω' := fun h => hΩ'0 0 h rfl
    have hχ0 : χ 0 = 0 := image_eq_zero_of_notMem_tsupport (fun hmem => h0KΦ (hχts hmem))
    have hcwne : ∀ w : ℂ, w ≠ 0 → (starRingEnd ℂ) w ≠ 0 := by
      intro w hw
      rw [starRingEnd_apply]
      exact star_ne_zero.mpr hw
    constructor
    · -- the `∂`-identity
      have hpt : ∀ w : ℂ, ((‖w‖ ^ 4)⁻¹ : ℝ) • (dz Φ w⁻¹ * (-w⁻¹ ^ 2 * u w⁻¹⁻¹))
          = dz (fun w => ((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * χ w) w * u w
            - ((starRingEnd ℂ w) ^ 2)⁻¹ * (-(2 * w ^ 1) * (((w ^ 2) ^ 2)⁻¹)) * χ w * u w := by
        intro w
        rcases eq_or_ne w 0 with rfl | hw
        · have hdz0 : dz (fun w => ((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * χ w) 0 = 0 :=
            (hfd0 _ 0 (fun hmem => h0Ω' (hΞts hmem))).1
          rw [hdz0, zero_mul]
          simp
        · have hconj := hcwne w hw
          have e1 : dz Φ w⁻¹ = -(w ^ 2) * dz χ w := by
            rw [hχdz w hw]
            field_simp
          rw [Complex.real_smul, hcast w, inv_inv, e1, hΞdz w hw]
          field_simp
          ring
      have hpt2 : ∀ w : ℂ, ((‖w‖ ^ 4)⁻¹ : ℝ) • (Φ w⁻¹ * A w⁻¹)
          = (((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * χ w) * P w
            + (((starRingEnd ℂ w) ^ 2)⁻¹ * (-(2 * w ^ 1) * (((w ^ 2) ^ 2)⁻¹)) * χ w) * u w := by
        intro w
        rcases eq_or_ne w 0 with rfl | hw
        · rw [show χ (0 : ℂ) = 0 from hχ0]
          simp
        · have hconj := hcwne w hw
          have hχw : Φ w⁻¹ = χ w := rfl
          rw [Complex.real_smul, hcast w, hχw]
          simp only [hAdef, hPdef]
          rw [inv_inv]
          field_simp
          ring
      have hcsdz : HasCompactSupport
          (fun w => dz (fun w => ((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * χ w) w) :=
        IsCompact.of_isClosed_subset hΞcs (isClosed_tsupport _) (hdzsupp _).1
      have hint1 : Integrable (fun w =>
          dz (fun w => ((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * χ w) w * u w) volume :=
        integC _ (hcontdz _ hΞsm).1 hcsdz ((hdzsupp _).1.trans hΞts) huloc
      have hint2 : Integrable (fun w =>
          ((starRingEnd ℂ w) ^ 2)⁻¹ * (-(2 * w ^ 1) * (((w ^ 2) ^ 2)⁻¹)) * χ w * u w)
          volume :=
        integC _ hΛsm.continuous hΛcs hΛts huloc
      have hint3 : Integrable (fun w =>
          (((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * χ w) * P w) volume :=
        integC _ hΞsm.continuous hΞcs hΞts hPloc
      have hRHS : ∫ z, Φ z * A z
          = (∫ w, (((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * χ w) * P w)
            + ∫ w, (((starRingEnd ℂ w) ^ 2)⁻¹ * (-(2 * w ^ 1) * (((w ^ 2) ^ 2)⁻¹)) * χ w)
              * u w := by
        calc ∫ z, Φ z * A z
            = ∫ w, ((‖w‖ ^ 4)⁻¹ : ℝ) • (Φ w⁻¹ * A w⁻¹) :=
              hcovFull _ (fun z hz => by rw [image_eq_zero_of_notMem_tsupport hz, zero_mul])
          _ = ∫ w, ((((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * χ w) * P w
              + (((starRingEnd ℂ w) ^ 2)⁻¹ * (-(2 * w ^ 1) * (((w ^ 2) ^ 2)⁻¹)) * χ w)
                * u w) := integral_congr_ae (ae_of_all _ hpt2)
          _ = _ := integral_add hint3 hint2
      calc ∫ z, dz Φ z * (-z ^ 2 * u z⁻¹)
          = ∫ w, ((‖w‖ ^ 4)⁻¹ : ℝ) • (dz Φ w⁻¹ * (-w⁻¹ ^ 2 * u w⁻¹⁻¹)) :=
            hcovFull _ (fun z hz => by rw [(hfd0 Φ z hz).1, zero_mul])
        _ = ∫ w, (dz (fun w => ((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * χ w) w * u w
            - ((starRingEnd ℂ w) ^ 2)⁻¹ * (-(2 * w ^ 1) * (((w ^ 2) ^ 2)⁻¹)) * χ w * u w) :=
            integral_congr_ae (ae_of_all _ hpt)
        _ = (∫ w, dz (fun w => ((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * χ w) w * u w)
            - ∫ w, ((starRingEnd ℂ w) ^ 2)⁻¹ * (-(2 * w ^ 1) * (((w ^ 2) ^ 2)⁻¹)) * χ w
              * u w := integral_sub hint1 hint2
        _ = (-∫ w, (((starRingEnd ℂ w) ^ 2)⁻¹ * (w ^ 2)⁻¹ * χ w) * P w)
            - ∫ w, ((starRingEnd ℂ w) ^ 2)⁻¹ * (-(2 * w ^ 1) * (((w ^ 2) ^ 2)⁻¹)) * χ w
              * u w := by rw [hU1 _ hΞsm hΞcs hΞts]
        _ = -∫ z, Φ z * A z := by rw [hRHS]; ring
    · -- the `∂̄`-identity
      have hpt : ∀ w : ℂ, ((‖w‖ ^ 4)⁻¹ : ℝ) • (dzbar Φ w⁻¹ * (-w⁻¹ ^ 2 * u w⁻¹⁻¹))
          = dzbar (fun w => (w ^ 4)⁻¹ * χ w) w * u w := by
        intro w
        rcases eq_or_ne w 0 with rfl | hw
        · have hdz0 : dzbar (fun w => (w ^ 4)⁻¹ * χ w) 0 = 0 :=
            (hfd0 _ 0 (fun hmem => h0Ω' (hΘts hmem))).2
          rw [hdz0, zero_mul]
          simp
        · have hconj := hcwne w hw
          have e2 : dzbar Φ w⁻¹ = -((starRingEnd ℂ w) ^ 2) * dzbar χ w := by
            rw [hχdzbar w hw]
            field_simp
          rw [Complex.real_smul, hcast w, inv_inv, e2, hΘdzbar w hw]
          field_simp
      have hpt2 : ∀ w : ℂ, ((‖w‖ ^ 4)⁻¹ : ℝ) • (Φ w⁻¹ * B w⁻¹)
          = ((w ^ 4)⁻¹ * χ w) * Q w := by
        intro w
        rcases eq_or_ne w 0 with rfl | hw
        · rw [show χ (0 : ℂ) = 0 from hχ0]
          simp
        · have hconj := hcwne w hw
          have hχw : Φ w⁻¹ = χ w := rfl
          rw [Complex.real_smul, hcast w, hχw]
          simp only [hBdef, hQdef]
          rw [inv_inv, map_inv₀]
          field_simp
      have hRHS : ∫ z, Φ z * B z = ∫ w, ((w ^ 4)⁻¹ * χ w) * Q w := by
        calc ∫ z, Φ z * B z
            = ∫ w, ((‖w‖ ^ 4)⁻¹ : ℝ) • (Φ w⁻¹ * B w⁻¹) :=
              hcovFull _ (fun z hz => by rw [image_eq_zero_of_notMem_tsupport hz, zero_mul])
          _ = ∫ w, ((w ^ 4)⁻¹ * χ w) * Q w := integral_congr_ae (ae_of_all _ hpt2)
      calc ∫ z, dzbar Φ z * (-z ^ 2 * u z⁻¹)
          = ∫ w, ((‖w‖ ^ 4)⁻¹ : ℝ) • (dzbar Φ w⁻¹ * (-w⁻¹ ^ 2 * u w⁻¹⁻¹)) :=
            hcovFull _ (fun z hz => by rw [(hfd0 Φ z hz).2, zero_mul])
        _ = ∫ w, dzbar (fun w => (w ^ 4)⁻¹ * χ w) w * u w :=
            integral_congr_ae (ae_of_all _ hpt)
        _ = -∫ w, ((w ^ 4)⁻¹ * χ w) * Q w := hU2 _ hΘsm hΘcs hΘts
        _ = -∫ z, Φ z * B z := by rw [hRHS]
  /- ### From the Wirtinger identities to the directional identities -/
  have hkey : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ z, ((fderiv ℝ φ z) 1) • (-z ^ 2 * u z⁻¹) = -∫ z, φ z • (A z + B z)) ∧
      (∫ z, ((fderiv ℝ φ z) Complex.I) • (-z ^ 2 * u z⁻¹)
        = -∫ z, φ z • (Complex.I * (A z - B z))) := by
    intro φ hφ hφcs hφts
    set Φ : ℂ → ℂ := fun z => ((φ z : ℝ) : ℂ) with hΦdef
    have hΦsm : ContDiff ℝ ∞ Φ := Complex.ofRealCLM.contDiff.comp hφ
    have hΦcs : HasCompactSupport Φ := hφcs.comp_left Complex.ofReal_zero
    have hΦsupp : tsupport Φ ⊆ tsupport φ := by
      refine closure_minimal (fun z hz => subset_tsupport φ ?_) (isClosed_tsupport φ)
      simp only [Function.mem_support] at hz ⊢
      intro h0
      refine hz ?_
      simp only [hΦdef, h0, Complex.ofReal_zero]
    have hΦts : tsupport Φ ⊆ Ω := hΦsupp.trans hφts
    obtain ⟨w1, w2⟩ := hW Φ hΦsm hΦcs hΦts
    have hφdiff : ∀ z, DifferentiableAt ℝ φ z :=
      fun z => (hφ.differentiable (by norm_num)).differentiableAt
    have hfdΦ : ∀ (z : ℂ) (v₀ : ℂ), (fderiv ℝ Φ z) v₀ = (((fderiv ℝ φ z) v₀ : ℝ) : ℂ) := by
      intro z v₀
      have h1 : fderiv ℝ Φ z = Complex.ofRealCLM.comp (fderiv ℝ φ z) :=
        (Complex.ofRealCLM.hasFDerivAt.comp z (hφdiff z).hasFDerivAt).fderiv
      rw [h1]
      rfl
    have hdecomp1 : ∀ z : ℂ, (((fderiv ℝ φ z) 1 : ℝ) : ℂ) = dz Φ z + dzbar Φ z := by
      intro z
      rw [← hfdΦ z 1]
      simp only [dz, dzbar]
      ring
    have hdecompI : ∀ z : ℂ, (((fderiv ℝ φ z) Complex.I : ℝ) : ℂ)
        = Complex.I * dz Φ z - Complex.I * dzbar Φ z := by
      intro z
      rw [← hfdΦ z Complex.I]
      simp only [dz, dzbar]
      linear_combination ((fderiv ℝ Φ z) Complex.I) * Complex.I_mul_I
    have hΦAint : Integrable (fun z => Φ z * A z) volume :=
      integC _ hΦsm.continuous hΦcs hΦts hAloc
    have hΦBint : Integrable (fun z => Φ z * B z) volume :=
      integC _ hΦsm.continuous hΦcs hΦts hBloc
    have hdzint : Integrable (fun z => dz Φ z * (-z ^ 2 * u z⁻¹)) volume :=
      integC _ (hcontdz Φ hΦsm).1
        (IsCompact.of_isClosed_subset hΦcs (isClosed_tsupport _) (hdzsupp Φ).1)
        ((hdzsupp Φ).1.trans hΦts) hVloc
    have hdzbarint : Integrable (fun z => dzbar Φ z * (-z ^ 2 * u z⁻¹)) volume :=
      integC _ (hcontdz Φ hΦsm).2
        (IsCompact.of_isClosed_subset hΦcs (isClosed_tsupport _) (hdzsupp Φ).2)
        ((hdzsupp Φ).2.trans hΦts) hVloc
    constructor
    · calc ∫ z, ((fderiv ℝ φ z) 1) • (-z ^ 2 * u z⁻¹)
          = ∫ z, (dz Φ z * (-z ^ 2 * u z⁻¹) + dzbar Φ z * (-z ^ 2 * u z⁻¹)) := by
            refine integral_congr_ae (ae_of_all _ (fun z => ?_))
            simp only
            rw [Complex.real_smul, hdecomp1 z]
            ring
        _ = (∫ z, dz Φ z * (-z ^ 2 * u z⁻¹)) + ∫ z, dzbar Φ z * (-z ^ 2 * u z⁻¹) :=
            integral_add hdzint hdzbarint
        _ = (-∫ z, Φ z * A z) + -∫ z, Φ z * B z := by rw [w1, w2]
        _ = -((∫ z, Φ z * A z) + ∫ z, Φ z * B z) := by ring
        _ = -∫ z, (Φ z * A z + Φ z * B z) := by rw [integral_add hΦAint hΦBint]
        _ = -∫ z, φ z • (A z + B z) := by
            rw [neg_inj]
            refine integral_congr_ae (ae_of_all _ (fun z => ?_))
            simp only [hΦdef]
            rw [Complex.real_smul]
            ring
    · calc ∫ z, ((fderiv ℝ φ z) Complex.I) • (-z ^ 2 * u z⁻¹)
          = ∫ z, (Complex.I * (dz Φ z * (-z ^ 2 * u z⁻¹))
              - Complex.I * (dzbar Φ z * (-z ^ 2 * u z⁻¹))) := by
            refine integral_congr_ae (ae_of_all _ (fun z => ?_))
            simp only
            rw [Complex.real_smul, hdecompI z]
            ring
        _ = Complex.I * (∫ z, dz Φ z * (-z ^ 2 * u z⁻¹))
            - Complex.I * ∫ z, dzbar Φ z * (-z ^ 2 * u z⁻¹) := by
            rw [integral_sub (hdzint.const_mul _) (hdzbarint.const_mul _)]
            congr 1
            · exact integral_const_mul _ _
            · exact integral_const_mul _ _
        _ = Complex.I * (-∫ z, Φ z * A z) - Complex.I * -∫ z, Φ z * B z := by
            rw [w1, w2]
        _ = -(Complex.I * ((∫ z, Φ z * A z) - ∫ z, Φ z * B z)) := by ring
        _ = -(Complex.I * ∫ z, (Φ z * A z - Φ z * B z)) := by
            rw [integral_sub hΦAint hΦBint]
        _ = -∫ z, Complex.I * (Φ z * A z - Φ z * B z) := by
            rw [neg_inj]
            exact (integral_const_mul _ _).symm
        _ = -∫ z, φ z • (Complex.I * (A z - B z)) := by
            rw [neg_inj]
            refine integral_congr_ae (ae_of_all _ (fun z => ?_))
            simp only [hΦdef]
            rw [Complex.real_smul]
            ring
  /- ### The witnesses and the five obligations -/
  refine ⟨fun z => A z + B z, fun z => Complex.I * (A z - B z), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- weak `x`-derivative of `v` on `Ω`
    intro φ hφ hφcs hφts
    exact (hkey φ hφ hφcs hφts).1
  · -- weak `y`-derivative of `v` on `Ω`
    intro φ hφ hφcs hφts
    exact (hkey φ hφ hφcs hφts).2
  · -- `L²_loc` of the `x`-witness
    intro K hKΩ hKc
    exact (hA2 K hKΩ hKc).add (hB2 K hKΩ hKc)
  · -- `L²_loc` of the `y`-witness
    intro K hKΩ hKc
    exact ((hA2 K hKΩ hKc).sub (hB2 K hKΩ hKc)).const_mul Complex.I
  · -- the a.e. Wirtinger combination
    have haeQ2 : ∀ᵐ w ∂(volume : Measure ℂ), w ∈ Ω' → Q w = ν w := by
      filter_upwards [haeQ] with w hw hwΩ'
      simp only [hQdef]
      linear_combination (2⁻¹ : ℂ) * (hw hwΩ')
    have haeQ' : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω → Q z⁻¹ = ν z⁻¹ := by
      have h := haetransSet Ω' hΩ'0 (fun w => Q w = ν w) haeQ2
      rwa [himg] at h
    filter_upwards [haeQ'] with z hz hzΩ
    simp only [hBdef]
    rw [hz hzΩ]
    linear_combination (A z - z ^ 2 / (starRingEnd ℂ z) ^ 2 * ν z⁻¹) * Complex.I_mul_I

set_option maxHeartbeats 400000 in
-- The solver-correctness proof elaborates as one large declaration whose near/far
-- weak-derivative `have` chains exceed the default heartbeat budget.
/-- **The solver solves.** `dbarSolver μ` has weak `∂̄`-derivative `μ` on all
of `ℂ`, with locally square-integrable weak gradient. The near piece is
`hasWeakGradient_cauchyTransform` (whose witnesses are Beurling transforms,
hence `L²_loc`); the far piece combines the same identity in the infinity
chart with `hasL2WeakDzbar_inversion_transport` and the cancellation of the
two unimodular factors; the two pieces are glued by additivity of weak
derivatives. -/
theorem hasL2WeakDzbar_dbarSolver {μ : ℂ → ℂ}
    (hμ : AEMeasurable μ volume) (hb : eLpNormEssSup μ volume < ⊤) :
    HasL2WeakDzbar (dbarSolver μ) μ Set.univ := by
  classical
  -- `ℝ`-on-`ℂ` tower/continuity instances not found by default synthesis here
  have : IsScalarTower ℝ ℂ ℂ := IsScalarTower.right
  have : ContinuousSMul ℝ ℂ := by
    refine ⟨?_⟩
    have h : (fun p : ℝ × ℂ => p.1 • p.2) = fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p
      exact Complex.real_smul
    rw [h]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
  -- ==================================================================
  -- ALGEBRA (far-piece bookkeeping, sign-checked end to end):
  -- write `h₁ := ballTruncation μ`, `ν := inftyChartCoeff μ`,
  -- `P₁ := P h₁`, `P₂ := P ν`, and `V z := -z²·P₂(z⁻¹)`, so that
  -- `dbarSolver μ z = P₁ z + V z` (`-z²·u = -(z²·u)`, matching the
  -- `−z²·u(1/z)` shape of the transport lemma).  CT5 gives `∂̄P₁ = h₁`
  -- and `∂̄P₂ = ν` weakly on `ℂ`; the inversion transport turns the
  -- latter into `∂̄V = τ` weakly on `{0}ᶜ`, `τ z = (z²/z̄²)·ν(z⁻¹)`.
  -- Unfolding `ν` at `z⁻¹`:
  --  · `1 < |z|` (so `z⁻¹ ∈ ball 0 1 ∖ {0}`):
  --      `ν(z⁻¹) = (z⁻¹)²/(conj z⁻¹)²·μ((z⁻¹)⁻¹) = (z̄²/z²)·μ z`
  --    (`inv_inv`, `map_inv₀`), hence `τ z = (z²/z̄²)(z̄²/z²)μ z = μ z`;
  --  · `0 < |z| ≤ 1` (so `|z⁻¹| ≥ 1`, outside the OPEN ball):
  --      `ν(z⁻¹) = 0`, hence `τ z = 0`.
  -- Since `h₁ = μ` on `closedBall 0 1` and `0` outside, for EVERY
  -- `z ≠ 0`: `h₁ z + τ z = μ z` (the circle `|z|=1` is covered by the
  -- closed/open ball asymmetry, no null-set argument needed there).
  -- At `z = 0` the transported data is silent, but `V` is holomorphic
  -- on `ball 0 1`: `P₂` is holomorphic off `closedBall 0 1` (Weyl, the
  -- coefficient vanishes there), the inversion composes, and the
  -- singularity at `0` is removable since `V` is continuous.  A smooth
  -- bump (`≡1` on `closedBall 0 ¼`, support in `ball 0 ½`) glues the
  -- classical gradient of `V` on `ball 0 1` with the transported weak
  -- gradient on `{0}ᶜ`; the glued witnesses are defined piecewise
  -- across the null circle `|z| = ½`.
  -- ==================================================================
  -- ===== inversion measure theory (as in the earlier theorems) =====
  have hinv_image_null : ∀ N : Set ℂ, volume N = 0 →
      volume ((fun z : ℂ => z⁻¹) '' N) = 0 := by
    intro N hN
    have hsub : (fun z : ℂ => z⁻¹) '' N
        ⊆ ((fun z : ℂ => z⁻¹) '' (N \ {0})) ∪ {0} := by
      rintro _ ⟨z, hz, rfl⟩
      by_cases h0 : z = 0
      · exact Or.inr (by simp [h0])
      · exact Or.inl ⟨z, ⟨hz, h0⟩, rfl⟩
    refine measure_mono_null hsub (measure_union_null ?_ (measure_singleton 0))
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ?_ (measure_mono_null Set.sdiff_subset hN)
    intro z hz
    exact (differentiableAt_inv (𝕜 := ℝ) (by simpa using hz.2)).differentiableWithinAt
  have hqmp : Measure.QuasiMeasurePreserving (fun z : ℂ => z⁻¹)
      (volume : Measure ℂ) volume := by
    refine ⟨measurable_inv, Measure.AbsolutelyContinuous.mk fun N hNm hN => ?_⟩
    rw [Measure.map_apply measurable_inv hNm]
    have hpre : (fun z : ℂ => z⁻¹) ⁻¹' N = (fun z : ℂ => z⁻¹) '' N := by
      ext w
      constructor
      · intro hw
        exact ⟨w⁻¹, hw, inv_inv w⟩
      · rintro ⟨v, hv, rfl⟩
        simpa [Set.mem_preimage, inv_inv] using hv
    rw [hpre]
    exact hinv_image_null N hN
  -- ===== the two coefficient pieces are in every `Lᵖ`, compactly vanishing =====
  have hball_eq : ballTruncation μ = (Metric.closedBall (0:ℂ) 1).indicator μ := by
    funext w
    by_cases hw : w ∈ Metric.closedBall (0:ℂ) 1
    · rw [Set.indicator_of_mem hw]
      simp only [ballTruncation]
      rw [if_pos hw]
    · rw [Set.indicator_of_notMem hw]
      simp only [ballTruncation]
      rw [if_neg hw]
  have hfin1 : IsFiniteMeasure (volume.restrict (Metric.closedBall (0:ℂ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hballmemP : ∀ p : ℝ≥0∞, MemLp (ballTruncation μ) p volume := by
    intro p
    rw [hball_eq, memLp_indicator_iff_restrict measurableSet_closedBall]
    have htop : MemLp μ ⊤ (volume.restrict (Metric.closedBall (0:ℂ) 1)) := by
      refine ⟨hμ.aestronglyMeasurable.restrict, ?_⟩
      rw [eLpNorm_exponent_top]
      exact lt_of_le_of_lt
        (eLpNormEssSup_mono_measure μ
          (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
        hb
    exact htop.mono_exponent le_top
  have hballsupp : ∀ w : ℂ, (1:ℝ) < ‖w‖ → ballTruncation μ w = 0 := by
    intro w hw
    simp only [ballTruncation]
    have hmem : w ∉ Metric.closedBall (0:ℂ) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hw
    rw [if_neg hmem]
  have hinftysupp : ∀ w : ℂ, (1:ℝ) < ‖w‖ → inftyChartCoeff μ w = 0 := by
    intro w hw
    simp only [inftyChartCoeff]
    have hmem : ¬ (w ∈ Metric.ball (0:ℂ) 1 ∧ w ≠ 0) := by
      rintro ⟨hw1, -⟩
      rw [Metric.mem_ball, dist_zero_right] at hw1
      linarith
    rw [if_neg hmem]
  have hg_aem : AEMeasurable
      (fun w : ℂ => w ^ 2 / (starRingEnd ℂ w) ^ 2 * μ w⁻¹) volume := by
    have h1 : Measurable fun w : ℂ => w ^ 2 / (starRingEnd ℂ w) ^ 2 := by
      simp only [div_eq_mul_inv]
      exact (measurable_id.pow_const 2).mul
        ((Complex.continuous_conj.measurable.pow_const 2).inv)
    have h2 : AEMeasurable (fun w : ℂ => μ w⁻¹) volume :=
      hμ.comp_quasiMeasurePreserving hqmp
    exact h1.aemeasurable.mul h2
  have hinfty_eq : inftyChartCoeff μ
      = (Metric.ball (0:ℂ) 1 \ {0}).indicator
          (fun w : ℂ => w ^ 2 / (starRingEnd ℂ w) ^ 2 * μ w⁻¹) := by
    funext w
    by_cases hw : w ∈ Metric.ball (0:ℂ) 1 ∧ w ≠ 0
    · rw [Set.indicator_of_mem ((Set.mem_sdiff w).mpr ⟨hw.1, by simpa using hw.2⟩)]
      simp only [inftyChartCoeff]
      rw [if_pos hw]
    · rw [Set.indicator_of_notMem
        (fun hmem => hw ⟨hmem.1, by simpa using hmem.2⟩)]
      simp only [inftyChartCoeff]
      rw [if_neg hw]
  have hfin2 : IsFiniteMeasure (volume.restrict (Metric.ball (0:ℂ) 1 \ {0})) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono Set.sdiff_subset) measure_ball_lt_top⟩
  have hinftymemP : ∀ p : ℝ≥0∞, MemLp (inftyChartCoeff μ) p volume := by
    intro p
    rw [hinfty_eq, memLp_indicator_iff_restrict
      (measurableSet_ball.diff (measurableSet_singleton 0))]
    refine MemLp.of_bound hg_aem.aestronglyMeasurable.restrict
      (eLpNormEssSup μ volume).toReal ?_
    have hCae : ∀ᵐ w ∂(volume : Measure ℂ),
        ‖μ w⁻¹‖ₑ ≤ eLpNormEssSup μ volume := by
      have h0 := enorm_ae_le_eLpNormEssSup μ (volume : Measure ℂ)
      rw [ae_iff] at h0 ⊢
      exact hqmp.preimage_null h0
    filter_upwards [ae_restrict_of_ae hCae] with w hw
    have hfac : ‖w ^ 2 / (starRingEnd ℂ w) ^ 2‖ ≤ 1 := by
      rcases eq_or_ne w 0 with rfl | hw0
      · simp
      · have hnz : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
        have h1 : ‖w ^ 2 / (starRingEnd ℂ w) ^ 2‖ = 1 := by
          rw [norm_div, norm_pow, norm_pow, Complex.norm_conj,
            div_self (pow_ne_zero 2 hnz)]
        exact h1.le
    calc ‖w ^ 2 / (starRingEnd ℂ w) ^ 2 * μ w⁻¹‖
        ≤ ‖μ w⁻¹‖ := by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) hfac
      _ ≤ (eLpNormEssSup μ volume).toReal := by
          rw [← ofReal_norm] at hw
          exact (ENNReal.ofReal_le_iff_le_toReal hb.ne).mp hw
  -- ===== the Cauchy-transform calculus for the two pieces =====
  have h24 : (2:ℝ≥0∞) < 4 := by norm_num
  have h4top : (4:ℝ≥0∞) ≠ ⊤ := by norm_num
  have hP1cont : Continuous (cauchyTransform (ballTruncation μ)) :=
    continuous_cauchyTransform_of_memLp_of_support h24 h4top (hballmemP 4) hballsupp
  have hP2cont : Continuous (cauchyTransform (inftyChartCoeff μ)) :=
    continuous_cauchyTransform_of_memLp_of_support h24 h4top (hinftymemP 4) hinftysupp
  obtain ⟨hP1x, hP1y⟩ :=
    hasWeakGradient_cauchyTransform h24 h4top (hballmemP 4) hballsupp
  obtain ⟨hP2x, hP2y⟩ :=
    hasWeakGradient_cauchyTransform h24 h4top (hinftymemP 4) hinftysupp
  -- `L²` classes and Wirtinger combinations of the CT witnesses
  have hS1x_mem : MemLp (fun z => beurling (ballTruncation μ) z + ballTruncation μ z)
      2 volume := (memLp_beurling (hballmemP 2)).add (hballmemP 2)
  have hS1y_mem : MemLp
      (fun z => Complex.I * (beurling (ballTruncation μ) z - ballTruncation μ z))
      2 volume := ((memLp_beurling (hballmemP 2)).sub (hballmemP 2)).const_mul Complex.I
  have hS2x_mem : MemLp (fun z => beurling (inftyChartCoeff μ) z + inftyChartCoeff μ z)
      2 volume := (memLp_beurling (hinftymemP 2)).add (hinftymemP 2)
  have hS2y_mem : MemLp
      (fun z => Complex.I * (beurling (inftyChartCoeff μ) z - inftyChartCoeff μ z))
      2 volume := ((memLp_beurling (hinftymemP 2)).sub (hinftymemP 2)).const_mul Complex.I
  have hcombS1 : ∀ z : ℂ,
      (beurling (ballTruncation μ) z + ballTruncation μ z)
        + Complex.I * (Complex.I * (beurling (ballTruncation μ) z - ballTruncation μ z))
        = 2 * ballTruncation μ z := by
    intro z
    linear_combination
      (beurling (ballTruncation μ) z - ballTruncation μ z) * Complex.I_mul_I
  have hcombS2 : ∀ z : ℂ,
      (beurling (inftyChartCoeff μ) z + inftyChartCoeff μ z)
        + Complex.I * (Complex.I * (beurling (inftyChartCoeff μ) z - inftyChartCoeff μ z))
        = 2 * inftyChartCoeff μ z := by
    intro z
    linear_combination
      (beurling (inftyChartCoeff μ) z - inftyChartCoeff μ z) * Complex.I_mul_I
  -- ===== the far vector-field piece `V` =====
  set V : ℂ → ℂ := fun z => -z ^ 2 * cauchyTransform (inftyChartCoeff μ) z⁻¹
    with hV_def
  have hVeq : (fun z : ℂ => dbarSolver μ z - cauchyTransform (ballTruncation μ) z)
      = V := by
    funext z
    simp only [hV_def, dbarSolver]
    ring
  have hVcont : Continuous V := by
    rw [← hVeq]
    exact ((isSphereVectorField_dbarSolver hμ hb).1).sub hP1cont
  -- ===== the transported weak `∂̄`-data on `{0}ᶜ` (BLACK BOX) =====
  have himg : (fun z : ℂ => z⁻¹) '' {(0:ℂ)}ᶜ = {(0:ℂ)}ᶜ := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa using inv_ne_zero (by simpa using hv)
    · intro hw
      exact ⟨w⁻¹, by simpa using inv_ne_zero (by simpa using hw), inv_inv w⟩
  have huimg : ContinuousOn (cauchyTransform (inftyChartCoeff μ))
      ((fun z : ℂ => z⁻¹) '' {(0:ℂ)}ᶜ) := hP2cont.continuousOn
  have hgradimg : HasL2WeakDzbar (cauchyTransform (inftyChartCoeff μ))
      (inftyChartCoeff μ) ((fun z : ℂ => z⁻¹) '' {(0:ℂ)}ᶜ) := by
    rw [himg]
    exact ⟨fun z => beurling (inftyChartCoeff μ) z + inftyChartCoeff μ z,
      fun z => Complex.I * (beurling (inftyChartCoeff μ) z - inftyChartCoeff μ z),
      ⟨hP2x.mono (Set.subset_univ _), hP2y.mono (Set.subset_univ _)⟩,
      fun K _ _ => hS2x_mem.restrict K, fun K _ _ => hS2y_mem.restrict K,
      Filter.Eventually.of_forall fun z _ => hcombS2 z⟩
  have hbb := hasL2WeakDzbar_inversion_transport isOpen_compl_singleton
    (subset_refl _) huimg hgradimg
  rw [← hV_def] at hbb
  obtain ⟨gxB, gyB, ⟨hgxB1, hgyB1⟩, hgxB2, hgyB2, hcombB⟩ := hbb
  -- ===== `V` is holomorphic on the unit ball =====
  have hS2x_LI : LocallyIntegrable
      (fun z => beurling (inftyChartCoeff μ) z + inftyChartCoeff μ z) volume :=
    hS2x_mem.locallyIntegrable (by norm_num)
  have hS2y_LI : LocallyIntegrable
      (fun z => Complex.I * (beurling (inftyChartCoeff μ) z - inftyChartCoeff μ z))
      volume := hS2y_mem.locallyIntegrable (by norm_num)
  have hP2out : DifferentiableOn ℂ (cauchyTransform (inftyChartCoeff μ))
      (Metric.closedBall (0:ℂ) 1)ᶜ := by
    refine weyl_lemma_on isClosed_closedBall.isOpen_compl hP2cont.continuousOn
      ⟨hP2x.mono (Set.subset_univ _), hP2y.mono (Set.subset_univ _)⟩
      (hS2x_LI.locallyIntegrableOn _) (hS2y_LI.locallyIntegrableOn _) ?_
    refine Filter.Eventually.of_forall fun z hz => ?_
    have hz1 : (1:ℝ) < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hz
    have hν0 : inftyChartCoeff μ z = 0 := hinftysupp z hz1
    have h9 := hcombS2 z
    linear_combination h9 + 2 * hν0
  have hVpunct : DifferentiableOn ℂ V (Metric.ball (0:ℂ) 1 \ {0}) := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    have hzin : z⁻¹ ∈ (Metric.closedBall (0:ℂ) 1)ᶜ := by
      have h1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.1
      have h0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le,
        norm_inv]
      exact one_lt_inv_iff₀.mpr ⟨h0, h1⟩
    have hd1 : DifferentiableAt ℂ (fun z : ℂ => -z ^ 2) z :=
      ((differentiable_pow 2).differentiableAt).neg
    have hd2 : DifferentiableAt ℂ
        (fun z : ℂ => cauchyTransform (inftyChartCoeff μ) z⁻¹) z := by
      have hP2at : DifferentiableAt ℂ (cauchyTransform (inftyChartCoeff μ)) z⁻¹ :=
        (hP2out z⁻¹ hzin).differentiableAt
          (isClosed_closedBall.isOpen_compl.mem_nhds hzin)
      exact hP2at.comp z (differentiableAt_inv (𝕜 := ℂ) hz0)
    exact (hd1.mul hd2).differentiableWithinAt
  have hVball : DifferentiableOn ℂ V (Metric.ball (0:ℂ) 1) :=
    (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).mp
      ⟨hVpunct, hVcont.continuousAt⟩
  have hVC1 : ContDiffOn ℝ 1 V (Metric.ball (0:ℂ) 1) :=
    ((hVball.analyticOnNhd isOpen_ball).contDiffOn
      isOpen_ball.uniqueDiffOn).restrict_scalars ℝ
  -- the classical gradient of the holomorphic `V` has vanishing Wirtinger `∂̄`
  have hwirt : ∀ z ∈ Metric.ball (0:ℂ) 1,
      (fderiv ℝ V z) 1 + Complex.I * (fderiv ℝ V z) Complex.I = 0 := by
    intro z hz
    have hd : DifferentiableAt ℂ V z :=
      (hVball z hz).differentiableAt (isOpen_ball.mem_nhds hz)
    have hres : fderiv ℝ V z = (fderiv ℂ V z).restrictScalars ℝ :=
      hd.fderiv_restrictScalars ℝ
    rw [hres]
    simp only [ContinuousLinearMap.coe_restrictScalars']
    have hIe : (fderiv ℂ V z) Complex.I = Complex.I * (fderiv ℂ V z) 1 := by
      have h1 : (fderiv ℂ V z) Complex.I = (fderiv ℂ V z) (Complex.I • 1) := by
        rw [smul_eq_mul, mul_one]
      rw [h1, map_smul, smul_eq_mul]
    rw [hIe]
    linear_combination ((fderiv ℂ V z) 1) * Complex.I_mul_I
  have hclassx : HasWeakDirDeriv 1 (fun z => (fderiv ℝ V z) 1) V
      (Metric.ball (0:ℂ) 1) := HasWeakDirDeriv.of_contDiffOn isOpen_ball hVC1
  have hclassy : HasWeakDirDeriv Complex.I (fun z => (fderiv ℝ V z) Complex.I) V
      (Metric.ball (0:ℂ) 1) := HasWeakDirDeriv.of_contDiffOn isOpen_ball hVC1
  have hcxBc : ContinuousOn (fun z => (fderiv ℝ V z) 1) (Metric.ball (0:ℂ) 1) :=
    (hVC1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply continuousOn_const
  have hcyBc : ContinuousOn (fun z => (fderiv ℝ V z) Complex.I)
      (Metric.ball (0:ℂ) 1) :=
    (hVC1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply continuousOn_const
  -- ===== the transported coefficient is exactly `μ − h₁` off the origin =====
  have hcoeff : ∀ z : ℂ, z ≠ 0 →
      z ^ 2 / (starRingEnd ℂ z) ^ 2 * inftyChartCoeff μ z⁻¹
        = μ z - ballTruncation μ z := by
    intro z hz
    have hzc : starRingEnd ℂ z ≠ 0 := fun h => hz (star_eq_zero.mp h)
    have h0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    simp only [inftyChartCoeff, ballTruncation]
    rcases le_or_gt ‖z‖ 1 with hle | hgt
    · have h1 : ¬ (z⁻¹ ∈ Metric.ball (0:ℂ) 1 ∧ z⁻¹ ≠ 0) := by
        rintro ⟨hball, -⟩
        rw [Metric.mem_ball, dist_zero_right, norm_inv] at hball
        have := (inv_lt_one₀ h0).mp hball
        linarith
      have h2 : z ∈ Metric.closedBall (0:ℂ) 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hle
      rw [if_neg h1, if_pos h2]
      ring
    · have h1 : z⁻¹ ∈ Metric.ball (0:ℂ) 1 ∧ z⁻¹ ≠ 0 := by
        refine ⟨?_, inv_ne_zero hz⟩
        rw [Metric.mem_ball, dist_zero_right, norm_inv]
        exact (inv_lt_one₀ h0).mpr hgt
      have h2 : z ∉ Metric.closedBall (0:ℂ) 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hgt
      rw [if_pos h1, if_neg h2, inv_inv, map_inv₀, inv_pow, inv_pow]
      have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
      have hzc2 : (starRingEnd ℂ z) ^ 2 ≠ 0 := pow_ne_zero 2 hzc
      field_simp
      ring
  -- ===== the gluing engine =====
  have hglue : ∀ (v : ℂ) (gB cB : ℂ → ℂ),
      HasWeakDirDeriv v gB V {(0:ℂ)}ᶜ →
      HasWeakDirDeriv v cB V (Metric.ball (0:ℂ) 1) →
      MemLpLocOn gB 2 {(0:ℂ)}ᶜ →
      ContinuousOn cB (Metric.ball (0:ℂ) 1) →
      HasWeakDirDeriv v
        (fun z => if z ∈ Metric.ball (0:ℂ) (1/2) then cB z else gB z) V Set.univ := by
    intro v gB cB hgB hcB hgB2 hcBc
    have hgB_int : ∀ K : Set ℂ, K ⊆ {(0:ℂ)}ᶜ → IsCompact K →
        IntegrableOn gB K volume := by
      intro K hK hKc
      have : IsFiniteMeasure (volume.restrict K) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
      exact memLp_one_iff_integrable.mp
        ((hgB2 K hK hKc).mono_exponent (by norm_num : (1:ℝ≥0∞) ≤ 2))
    -- the two witnesses agree a.e. on the punctured ball (uniqueness)
    have hae : ∀ᵐ z ∂(volume : Measure ℂ),
        z ∈ Metric.ball (0:ℂ) 1 \ {0} → gB z = cB z := by
      refine HasWeakDirDeriv.ae_eq (isOpen_ball.sdiff isClosed_singleton)
        (hgB.mono fun z hz => hz.2) (hcB.mono Set.sdiff_subset) ?_ ?_
      · rw [MeasureTheory.locallyIntegrableOn_iff
          (isOpen_ball.sdiff isClosed_singleton).isLocallyClosed]
        intro k hk hkc
        exact hgB_int k (fun z hz => (hk hz).2) hkc
      · exact (hcBc.mono Set.sdiff_subset).locallyIntegrableOn
          (measurableSet_ball.diff (measurableSet_singleton 0))
    -- null sphere for the piecewise seam
    have hnullsphere : ∀ᵐ z ∂(volume : Measure ℂ),
        z ∉ Metric.sphere (0:ℂ) (1/2) := by
      rw [ae_iff]
      have hset : {z : ℂ | ¬ z ∉ Metric.sphere (0:ℂ) (1/2)}
          = Metric.sphere (0:ℂ) (1/2) := by
        ext z; simp
      rw [hset]
      exact Measure.addHaar_sphere volume 0 (1/2)
    -- the smooth two-chart partition of the test function
    intro φ hφ hcs _
    set η : ContDiffBump (0:ℂ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩ with hη_def
    have hφ₁_cd : ContDiff ℝ ∞ (fun z => η z * φ z) := η.contDiff.mul hφ
    have hφ₂_cd : ContDiff ℝ ∞ (fun z => φ z - η z * φ z) :=
      hφ.sub (η.contDiff.mul hφ)
    have hφ₁_cs : HasCompactSupport (fun z => η z * φ z) := hcs.mul_left
    have hφ₂_cs : HasCompactSupport (fun z => φ z - η z * φ z) := hcs.sub hcs.mul_left
    have hts₁c : tsupport (fun z => η z * φ z) ⊆ Metric.closedBall (0:ℂ) (1/2) := by
      refine closure_minimal ?_ isClosed_closedBall
      intro z hz
      have hηz : η z ≠ 0 := by
        intro h0
        apply hz
        simp [h0]
      have hzs : z ∈ Function.support (η : ℂ → ℝ) := hηz
      rw [η.support_eq] at hzs
      exact Metric.ball_subset_closedBall hzs
    have hts₁ : tsupport (fun z => η z * φ z) ⊆ Metric.ball (0:ℂ) 1 :=
      hts₁c.trans (Metric.closedBall_subset_ball (by norm_num))
    have hts₂q : tsupport (fun z => φ z - η z * φ z) ⊆ {z : ℂ | 1/4 ≤ ‖z‖} := by
      refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
      intro z hz
      by_contra hlt
      simp only [Set.mem_ofPred_eq, not_le] at hlt
      have hz14 : z ∈ Metric.closedBall (0:ℂ) (1/4 : ℝ) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hlt.le
      have hη1 : η z = 1 := η.one_of_mem_closedBall hz14
      apply hz
      simp [hη1]
    have hts₂ : tsupport (fun z => φ z - η z * φ z) ⊆ {(0:ℂ)}ᶜ := by
      refine hts₂q.trans ?_
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h0
      rw [h0, norm_zero] at hz
      linarith
    -- integrability of the compactly supported pairings against `V`
    have hint : ∀ (ψ : ℂ → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        Integrable (fun z => ((fderiv ℝ ψ z) v) • V z) volume := by
      intro ψ hψ hψcs
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).smul
          hVcont
      · exact (HasCompactSupport.fderiv_apply ℝ hψcs v).smul_right
    -- fderiv splits along the partition
    have hdφ : ∀ z, (fderiv ℝ φ z) v
        = (fderiv ℝ (fun z => η z * φ z) z) v
          + (fderiv ℝ (fun z => φ z - η z * φ z) z) v := by
      intro z
      have h1 : DifferentiableAt ℝ (fun z => η z * φ z) z :=
        (hφ₁_cd.differentiable (by norm_num)).differentiableAt
      have h2 : DifferentiableAt ℝ (fun z => φ z - η z * φ z) z :=
        (hφ₂_cd.differentiable (by norm_num)).differentiableAt
      have h3 : φ = fun z => (η z * φ z) + (φ z - η z * φ z) := by
        funext w
        ring
      nth_rewrite 1 [h3]
      rw [fderiv_fun_add h1 h2]
      simp
    have hLHS : ∫ z, ((fderiv ℝ φ z) v) • V z
        = (∫ z, ((fderiv ℝ (fun z => η z * φ z) z) v) • V z)
          + ∫ z, ((fderiv ℝ (fun z => φ z - η z * φ z) z) v) • V z := by
      rw [← integral_add (hint _ hφ₁_cd hφ₁_cs) (hint _ hφ₂_cd hφ₂_cs)]
      apply integral_congr_ae
      filter_upwards with z
      rw [hdφ z]
      module
    have h1 := hcB _ hφ₁_cd hφ₁_cs hts₁
    have h2 := hgB _ hφ₂_cd hφ₂_cs hts₂
    -- the near pairing sees the glued witness through the seam
    have haeeq1 : (fun z => (η z * φ z) • cB z) =ᵐ[volume]
        fun z => (η z * φ z) •
          (if z ∈ Metric.ball (0:ℂ) (1/2) then cB z else gB z) := by
      filter_upwards [hnullsphere] with z hzs
      by_cases hzb : z ∈ Metric.ball (0:ℂ) (1/2)
      · rw [if_pos hzb]
      · rw [if_neg hzb]
        by_cases hzsupp : z ∈ tsupport (fun z => η z * φ z)
        · exfalso
          apply hzs
          have hle : dist z 0 ≤ 1/2 := Metric.mem_closedBall.mp (hts₁c hzsupp)
          have hge : ¬ dist z 0 < 1/2 := fun h => hzb (Metric.mem_ball.mpr h)
          exact Metric.mem_sphere.mpr (le_antisymm hle (not_lt.mp hge))
        · rw [image_eq_zero_of_notMem_tsupport hzsupp]
          simp
    have haeeq2 : (fun z => (φ z - η z * φ z) • gB z) =ᵐ[volume]
        fun z => (φ z - η z * φ z) •
          (if z ∈ Metric.ball (0:ℂ) (1/2) then cB z else gB z) := by
      filter_upwards [hae] with z hz
      by_cases hzb : z ∈ Metric.ball (0:ℂ) (1/2)
      · rw [if_pos hzb]
        by_cases hzsupp : z ∈ tsupport (fun z => φ z - η z * φ z)
        · have h14 : (1/4:ℝ) ≤ ‖z‖ := hts₂q hzsupp
          have hz0 : z ≠ 0 := by
            intro h0
            rw [h0, norm_zero] at h14
            linarith
          have hz1 : z ∈ Metric.ball (0:ℂ) 1 :=
            Metric.ball_subset_ball (by norm_num) hzb
          rw [hz ⟨hz1, by simpa using hz0⟩]
        · rw [image_eq_zero_of_notMem_tsupport hzsupp]
          simp
      · rw [if_neg hzb]
    -- integrability for recombining the right-hand sides
    have hIntφ₁cB : Integrable (fun z => (η z * φ z) • cB z) volume := by
      have hK : IsCompact (tsupport (fun z => η z * φ z)) := hφ₁_cs
      have hon : IntegrableOn (fun z => (η z * φ z) • cB z)
          (tsupport (fun z => η z * φ z)) volume :=
        ((hcBc.mono hts₁).integrableOn_compact hK).continuousOn_smul
          (hφ₁_cd.continuous.continuousOn) hK
      refine (integrableOn_iff_integrable_of_support_subset ?_).mp hon
      intro z hz
      apply subset_tsupport
      simp only [Function.mem_support] at hz ⊢
      intro hmz
      apply hz
      rw [hmz]
      module
    have hIntφ₂gB : Integrable (fun z => (φ z - η z * φ z) • gB z) volume := by
      have hK : IsCompact (tsupport (fun z => φ z - η z * φ z)) := hφ₂_cs
      have hon : IntegrableOn (fun z => (φ z - η z * φ z) • gB z)
          (tsupport (fun z => φ z - η z * φ z)) volume :=
        (hgB_int _ hts₂ hK).continuousOn_smul
          (hφ₂_cd.continuous.continuousOn) hK
      refine (integrableOn_iff_integrable_of_support_subset ?_).mp hon
      intro z hz
      apply subset_tsupport
      simp only [Function.mem_support] at hz ⊢
      intro hmz
      apply hz
      rw [hmz]
      module
    calc ∫ z, ((fderiv ℝ φ z) v) • V z
        = (∫ z, ((fderiv ℝ (fun z => η z * φ z) z) v) • V z)
          + ∫ z, ((fderiv ℝ (fun z => φ z - η z * φ z) z) v) • V z := hLHS
      _ = (-∫ z, (η z * φ z) • cB z) + (-∫ z, (φ z - η z * φ z) • gB z) := by
          rw [h1, h2]
      _ = (-∫ z, (η z * φ z) •
              (if z ∈ Metric.ball (0:ℂ) (1/2) then cB z else gB z))
          + (-∫ z, (φ z - η z * φ z) •
              (if z ∈ Metric.ball (0:ℂ) (1/2) then cB z else gB z)) := by
          rw [integral_congr_ae haeeq1, integral_congr_ae haeeq2]
      _ = -((∫ z, (η z * φ z) •
              (if z ∈ Metric.ball (0:ℂ) (1/2) then cB z else gB z))
          + ∫ z, (φ z - η z * φ z) •
              (if z ∈ Metric.ball (0:ℂ) (1/2) then cB z else gB z)) := by
          ring
      _ = -∫ z, ((η z * φ z) •
              (if z ∈ Metric.ball (0:ℂ) (1/2) then cB z else gB z)
            + (φ z - η z * φ z) •
              (if z ∈ Metric.ball (0:ℂ) (1/2) then cB z else gB z)) := by
          rw [integral_add (hIntφ₁cB.congr haeeq1) (hIntφ₂gB.congr haeeq2)]
      _ = -∫ z, φ z •
            (if z ∈ Metric.ball (0:ℂ) (1/2) then cB z else gB z) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with z
          module
  -- ===== the glued witnesses are locally square-integrable =====
  have hGloc : ∀ (gB cB : ℂ → ℂ), MemLpLocOn gB 2 {(0:ℂ)}ᶜ →
      ContinuousOn cB (Metric.ball (0:ℂ) 1) →
      MemLpLocOn (fun z => if z ∈ Metric.ball (0:ℂ) (1/2) then cB z else gB z)
        2 Set.univ := by
    intro gB cB hgB2 hcBc K _ hKc
    have hGsplit : (fun z => if z ∈ Metric.ball (0:ℂ) (1/2) then cB z else gB z)
        = fun z => (Metric.ball (0:ℂ) (1/2)).indicator cB z
            + (Metric.ball (0:ℂ) (1/2))ᶜ.indicator gB z := by
      funext z
      by_cases hz : z ∈ Metric.ball (0:ℂ) (1/2)
      · rw [if_pos hz, Set.indicator_of_mem hz,
          Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hz)]
        ring
      · rw [if_neg hz, Set.indicator_of_notMem hz, Set.indicator_of_mem hz]
        ring
    rw [hGsplit]
    have hK1 : MemLp ((Metric.ball (0:ℂ) (1/2)).indicator cB) 2
        (volume.restrict K) := by
      rw [memLp_indicator_iff_restrict measurableSet_ball,
        Measure.restrict_restrict measurableSet_ball]
      have : IsFiniteMeasure (volume.restrict (Metric.ball (0:ℂ) (1/2) ∩ K)) :=
        ⟨by rw [Measure.restrict_apply_univ]
            exact lt_of_le_of_lt (measure_mono Set.inter_subset_right)
              hKc.measure_lt_top⟩
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0:ℂ) (1/2)).exists_bound_of_continuousOn
        (hcBc.mono (Metric.closedBall_subset_ball (by norm_num)))
      refine MemLp.of_bound ?_ C ?_
      · exact (hcBc.mono
          (fun z hz => Metric.ball_subset_ball (by norm_num) hz.1)).aestronglyMeasurable
          (measurableSet_ball.inter hKc.measurableSet)
      · filter_upwards [ae_restrict_mem (measurableSet_ball.inter hKc.measurableSet)]
          with z hz
        exact hC z (Metric.ball_subset_closedBall hz.1)
    have hK2 : MemLp ((Metric.ball (0:ℂ) (1/2))ᶜ.indicator gB) 2
        (volume.restrict K) := by
      rw [memLp_indicator_iff_restrict measurableSet_ball.compl,
        Measure.restrict_restrict measurableSet_ball.compl]
      refine hgB2 _ ?_ (hKc.inter_left isOpen_ball.isClosed_compl)
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h0
      exact hz.1 (by rw [h0]; exact Metric.mem_ball_self (by norm_num))
    exact hK1.add hK2
  -- ===== a weak derivative transfers along a pointwise equality =====
  have hfun_congr : ∀ {g f f' : ℂ → ℂ} {v : ℂ}, (∀ z, f z = f' z) →
      HasWeakDirDeriv v g f Set.univ → HasWeakDirDeriv v g f' Set.univ := by
    intro g f f' v hff' h φ hφ hcs hts
    rw [← h φ hφ hcs hts]
    apply integral_congr_ae
    filter_upwards with z
    rw [hff' z]
  -- ===== local integrability from local `L²` =====
  have hLI_of_loc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      LocallyIntegrable g volume := by
    intro g hg
    rw [locallyIntegrable_iff]
    intro k hk
    have : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hg k (Set.subset_univ k) hk).mono_exponent (by norm_num : (1:ℝ≥0∞) ≤ 2))
  -- ===== assemble the two glued directions =====
  have hVx : HasWeakDirDeriv 1
      (fun z => if z ∈ Metric.ball (0:ℂ) (1/2) then (fderiv ℝ V z) 1 else gxB z)
      V Set.univ := hglue 1 gxB _ hgxB1 hclassx hgxB2 hcxBc
  have hVy : HasWeakDirDeriv Complex.I
      (fun z => if z ∈ Metric.ball (0:ℂ) (1/2) then (fderiv ℝ V z) Complex.I
        else gyB z) V Set.univ := hglue Complex.I gyB _ hgyB1 hclassy hgyB2 hcyBc
  have hGxloc := hGloc gxB _ hgxB2 hcxBc
  have hGyloc := hGloc gyB _ hgyB2 hcyBc
  -- the glued Wirtinger combination equals `2(μ − h₁)` a.e.
  have hcombG : ∀ᵐ z ∂(volume : Measure ℂ),
      (if z ∈ Metric.ball (0:ℂ) (1/2) then (fderiv ℝ V z) 1 else gxB z)
        + Complex.I *
          (if z ∈ Metric.ball (0:ℂ) (1/2) then (fderiv ℝ V z) Complex.I else gyB z)
        = 2 * (μ z - ballTruncation μ z) := by
    filter_upwards [hcombB] with z hz
    by_cases hzb : z ∈ Metric.ball (0:ℂ) (1/2)
    · rw [if_pos hzb, if_pos hzb]
      have hz1 : z ∈ Metric.ball (0:ℂ) 1 :=
        Metric.ball_subset_ball (by norm_num) hzb
      have hball : ballTruncation μ z = μ z := by
        simp only [ballTruncation]
        rw [if_pos (Metric.ball_subset_closedBall hz1)]
      rw [hwirt z hz1, hball]
      ring
    · rw [if_neg hzb, if_neg hzb]
      have hz0 : z ≠ 0 := fun h0 => hzb (by
        rw [h0]; exact Metric.mem_ball_self (by norm_num))
      have hz' := hz (by simpa using hz0)
      have hco := hcoeff z hz0
      beta_reduce at hz'
      linear_combination hz' + 2 * hco
  -- ===== final packaging =====
  refine ⟨fun z => (beurling (ballTruncation μ) z + ballTruncation μ z)
      + (if z ∈ Metric.ball (0:ℂ) (1/2) then (fderiv ℝ V z) 1 else gxB z),
    fun z => Complex.I * (beurling (ballTruncation μ) z - ballTruncation μ z)
      + (if z ∈ Metric.ball (0:ℂ) (1/2) then (fderiv ℝ V z) Complex.I else gyB z),
    ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine hfun_congr (f := fun z => cauchyTransform (ballTruncation μ) z + V z)
      (fun z => by simp only [hV_def, dbarSolver]; ring) ?_
    exact HasWeakDirDeriv.add hP1x hVx
      (hP1cont.locallyIntegrable.locallyIntegrableOn _)
      (hVcont.locallyIntegrable.locallyIntegrableOn _)
      ((hS1x_mem.locallyIntegrable (by norm_num)).locallyIntegrableOn _)
      ((hLI_of_loc hGxloc).locallyIntegrableOn _)
  · refine hfun_congr (f := fun z => cauchyTransform (ballTruncation μ) z + V z)
      (fun z => by simp only [hV_def, dbarSolver]; ring) ?_
    exact HasWeakDirDeriv.add hP1y hVy
      (hP1cont.locallyIntegrable.locallyIntegrableOn _)
      (hVcont.locallyIntegrable.locallyIntegrableOn _)
      ((hS1y_mem.locallyIntegrable (by norm_num)).locallyIntegrableOn _)
      ((hLI_of_loc hGyloc).locallyIntegrableOn _)
  · exact fun K hK hKc => (hS1x_mem.restrict K).add (hGxloc K hK hKc)
  · exact fun K hK hKc => (hS1y_mem.restrict K).add (hGyloc K hK hKc)
  · filter_upwards [hcombG] with z hz _
    have h1 := hcombS1 z
    linear_combination h1 + hz

end NoWanderingDomains
