/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.GehringHigherIntegrability.SelfImprovementCore

/-!
# Gehring self-improvement: the abstract reverse-Hölder lemma (S2, part II)

The collar-free good-λ companion `gehring_goodLambda_integral_noCollar`, the `Žₙ`-truncation
hole-filling pillars (`gehring_mass_layerCake`, `gehring_crux_le`, `gehring_assembly`,
`gehring_holeFill`, …), and the assembled abstract Gehring self-improvement lemma
`gehring_selfImprovement`: a nonnegative reverse-Hölder weight gains a higher integrability
exponent `q + ε`.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology Real Pointwise

namespace NoWanderingDomains

/-- **Collar-free honest exponent-1 good-λ** (the high-`λ₁` companion of
`gehring_goodLambda_integral_core`).  For levels `lam` above the structural threshold
`λ₁` (encoded by `hλ₁ : 5·√Wm ≤ (s−t)·lam^{q/2}`, where `Wm = (∫_{16B₀}wᵠ).toReal`), **no
boundary cube meets `ball x₀ t`**: a stopping cube `Qᵢ` meeting `ball x₀ t` has, by the
stopping lower bound `lamᵠ·vol(Qᵢ) ≤ ∫_{ball s}wᵠ ≤ Wm`, side `ρᵢ ≤ √Wm/lam^{q/2} ≤ (s−t)/5`,
so its `4×` enlargement `Eᵢ = ball cᵢ(4ρᵢ) ⊆ ball x₀(t+5ρᵢ) ⊆ ball x₀ s` is engine-able.
Hence the boundary collar of the core vanishes on the `ball t` super-level set, giving the
collar-FREE good-λ that the consumer integrates on the high range `(λ₁,∞)`. -/
private theorem gehring_goodLambda_integral_noCollar {q A : ℝ} (hq : 1 < q) (hA : 0 ≤ A)
    {w b : ℂ → ℝ≥0∞} (hwmeas : AEMeasurable w volume) (hbmeas : AEMeasurable b volume)
    (hRH : ∀ (x : ℂ) (r : ℝ), 0 < r →
      (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
        ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
          ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q))
    (x₀ : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hWfin : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤)
    (hBfin : ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ q < ⊤)
    (t s : ℝ) (ht : 4 * R₀ ≤ t) (hts : t < s) (hs : s ≤ 16 * R₀)
    (lam : ℝ) (hlam : 0 < lam)
    (hlam0cond : (⨍⁻ z in Metric.ball x₀ s, w z ^ q ∂volume) ≤ (ENNReal.ofReal lam) ^ q)
    (hlam1 : 5 * Real.sqrt ((∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal)
            ≤ (s - t) * lam ^ (q / 2)) :
    ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (w z).toReal}, w z ^ q
      ≤ ENNReal.ofReal (256 * (Real.pi ^ (1 / q) * A + 1) * lam ^ (q - 1))
          * (∫⁻ z in Metric.ball x₀ s ∩
              {z | 1 / (4 * (Real.pi ^ (1 / q) * A + 1)) * lam < (w z).toReal}, w z)
        + ENNReal.ofReal (64 * (4 * (Real.pi ^ (1 / q) * A + 1)) ^ q)
          * (∫⁻ z in Metric.ball x₀ s ∩
              {z | 1 / (4 * (Real.pi ^ (1 / q) * A + 1)) * lam < (b z).toReal}, b z ^ q) := by
  classical
  have hq0 : 0 < q := lt_trans one_pos hq
  have hst : 0 < s - t := by linarith
  have hspos : 0 < s := by linarith
  -- Planar doubling instance for the Carleson engine.
  have hdbl : (volume : Measure ℂ).IsDoubling (2 ^ Module.finrank ℝ ℂ) :=
    InnerProductSpace.IsDoubling
  -- Abbreviation `Ã = π^{1/q}·A + 1 > 0` (the reverse-Hölder constant, padded by 1).
  set P : ℝ := Real.pi ^ (1 / q) with hPdef
  have hPpos : 0 < P := by rw [hPdef]; positivity
  set Ã : ℝ := P * A + 1 with hÃdef
  have hÃpos : 0 < Ã := by rw [hÃdef]; nlinarith [hPpos, hA]
  -- The collar/level constants: `β = 1/(4Ã)`, w-level `lw = ofReal(βlam)`,
  -- b-level `lb = ofReal((βlam)^q)`.
  set β : ℝ := 1 / (4 * Ã) with hβdef
  have hβpos : 0 < β := by rw [hβdef]; positivity
  set lw : ℝ≥0∞ := ENNReal.ofReal (β * lam) with hlwdef
  set lb : ℝ≥0∞ := ENNReal.ofReal ((β * lam) ^ q) with hlbdef
  -- Choose `M` minimal-ish with `2s ≤ 2^M` (any large enough `M` works for the cover).
  obtain ⟨M, hM⟩ : ∃ M : ℤ, 2 * s ≤ (2 : ℝ) ^ M := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * s) (by norm_num : (1:ℝ) < 2)
    exact ⟨(n : ℤ), by rw [zpow_natCast]; exact hn.le⟩
  -- Run the global dyadic cover.
  obtain ⟨B, hBct, hBdisj, hBscale, hBmeet, hBcov, hBup, hBlow⟩ :=
    gehring_dyadic_global_cover hq0 hwmeas x₀ s hspos M hM lam hlam hlam0cond
  -- Geometry of a cube `i ∈ B`: centre, scale, enlarged ball `Eᵢ = ball cᵢ (4·2^{nᵢ})`.
  set cI : ℤ × (ℤ × ℤ) → ℂ := fun i => dyadicCenter i.1 i.2 with hcIdef
  set ρI : ℤ × (ℤ × ℤ) → ℝ := fun i => (2 : ℝ) ^ i.1 with hρIdef
  have hρIpos : ∀ i, 0 < ρI i := fun i => by rw [hρIdef]; exact zpow_pos (by norm_num) _
  -- The cube is inside its circumscribed ball `ball cᵢ (2^{nᵢ})`.
  have hQsubball : ∀ i, dyadicSquare i.1 i.2 ⊆ Metric.ball (cI i) (ρI i) := by
    intro i; rw [hcIdef, hρIdef]; exact dyadicSquare_subset_ball i.1 i.2
  -- ============================================================================
  -- PER-CUBE REVERSE-HÖLDER DICHOTOMY (super-level concentrated).
  -- For `i ∈ B`: either `w`-good (`lw·vol(Eᵢ) ≤ ∫_{Eᵢ∩{w>βλ}} w`) or `b`-good
  -- (`lb·vol(Eᵢ) ≤ ∫_{Eᵢ∩{b>βλ}} bᵠ`), where `Eᵢ = ball cᵢ (4ρᵢ)`.
  -- ============================================================================
  set Esub : Set ℂ := {z : ℂ | β * lam < (w z).toReal} with hEsubdef
  set Fsub : Set ℂ := {z : ℂ | β * lam < (b z).toReal} with hFsubdef
  -- Full (un-restricted) reverse-Hölder levels `lwf = lam/(2Ã)`, `lbf = (lam/(2Ã))^q`.
  set lwf : ℝ≥0∞ := ENNReal.ofReal (lam / (2 * Ã)) with hlwfdef
  set lbf : ℝ≥0∞ := ENNReal.ofReal ((lam / (2 * Ã)) ^ q) with hlbfdef
  have hdich : ∀ i ∈ B,
      (lwf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), w z) ∨
      (lbf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q) := by
    intro i hi
    -- `lam < (⨍_{Qᵢ} wᵠ)^{1/q}`.
    have hQpos : 0 < volume (dyadicSquare i.1 i.2) := by
      rw [volume_dyadicSquare, ENNReal.ofReal_pos]; positivity
    have hQtop : volume (dyadicSquare i.1 i.2) ≠ ⊤ := by
      rw [volume_dyadicSquare]; exact ENNReal.ofReal_ne_top
    have hlowfull : (ENNReal.ofReal lam) ^ q < ⨍⁻ z in dyadicSquare i.1 i.2, w z ^ q ∂volume := by
      refine lt_of_lt_of_le (hBlow i hi) ?_
      rw [setLAverage_eq]
      exact ENNReal.div_le_div_right (lintegral_mono_set Set.inter_subset_left) _
    have h1q : (0:ℝ) < 1 / q := by positivity
    have hroot : ENNReal.ofReal lam <
        (⨍⁻ z in dyadicSquare i.1 i.2, w z ^ q ∂volume) ^ (1 / q) := by
      have h := ENNReal.rpow_lt_rpow hlowfull h1q
      have hid : (ENNReal.ofReal lam ^ q) ^ (1 / q) = ENNReal.ofReal lam := by
        rw [one_div, ENNReal.rpow_rpow_inv hq0.ne']
      rwa [hid] at h
    -- Reverse-Hölder on the cube, with constant `P·A ≤ Ã`.
    have hRHc := dyadic_reverseHolder' hq hA hRH i.1 i.2
    have hPA_le : ENNReal.ofReal (P * A) ≤ ENNReal.ofReal Ã :=
      ENNReal.ofReal_le_ofReal (by rw [hÃdef, hPdef]; nlinarith [hPpos, hA])
    have hRHc' : ENNReal.ofReal lam <
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume) +
          ENNReal.ofReal Ã *
            (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q) := by
      have hceq : Metric.ball (dyadicCenter i.1 i.2) (4 * (2:ℝ) ^ i.1)
          = Metric.ball (cI i) (4 * ρI i) := by rw [hcIdef, hρIdef]
      rw [hceq] at hRHc
      refine lt_of_lt_of_le hroot (le_trans hRHc (add_le_add ?_ ?_)) <;>
        exact mul_le_mul_left hPA_le _
    -- One of the two terms is `≥ ofReal lam / 2`.
    have hvol4_pos : 0 < volume (Metric.ball (cI i) (4 * ρI i)) :=
      Metric.measure_ball_pos _ _ (by positivity [hρIpos i])
    have hvol4_ne : volume (Metric.ball (cI i) (4 * ρI i)) ≠ 0 := hvol4_pos.ne'
    have hvol4_top : volume (Metric.ball (cI i) (4 * ρI i)) ≠ ⊤ := measure_ball_lt_top.ne
    have hÃne : ENNReal.ofReal Ã ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hÃpos
    have hÃtop : ENNReal.ofReal Ã ≠ ⊤ := ENNReal.ofReal_ne_top
    have hhalf : ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume)
          ≥ ENNReal.ofReal lam / 2 ∨
        ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q)
          ≥ ENNReal.ofReal lam / 2 := by
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [not_le] at h1 h2
      have hsum2 : ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume) +
          ENNReal.ofReal Ã * (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q)
          < ENNReal.ofReal lam / 2 + ENNReal.ofReal lam / 2 := ENNReal.add_lt_add h1 h2
      rw [ENNReal.add_halves] at hsum2
      exact absurd (lt_trans hRHc' hsum2) (lt_irrefl _)
    -- `lwf · ofReal Ã = ofReal lam / 2`.
    have hlwf_mul : lwf * ENNReal.ofReal Ã = ENNReal.ofReal lam / 2 := by
      rw [hlwfdef, ← ENNReal.ofReal_mul (by positivity)]
      have hreal : lam / (2 * Ã) * Ã = lam / 2 := by field_simp
      rw [hreal, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      congr 1; norm_num
    rcases hhalf with hw | hb
    · left
      have hge : lwf ≤ ⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume := by
        have hchain : lwf * ENNReal.ofReal Ã
            ≤ (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), w z ∂volume) * ENNReal.ofReal Ã := by
          rw [hlwf_mul, mul_comm]; exact hw
        exact (ENNReal.mul_le_mul_iff_left hÃne hÃtop).mp hchain
      rw [setLAverage_eq] at hge
      rwa [ENNReal.le_div_iff_mul_le (Or.inl hvol4_ne) (Or.inl hvol4_top)] at hge
    · right
      have hlbf_eq : lbf = lwf ^ q := by
        rw [hlbfdef, hlwfdef, ← ENNReal.ofReal_rpow_of_pos (by positivity)]
      have hgew : lwf ≤ (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q) := by
        have hchain : lwf * ENNReal.ofReal Ã
            ≤ (⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume) ^ (1 / q)
                * ENNReal.ofReal Ã := by
          rw [hlwf_mul, mul_comm]; exact hb
        exact (ENNReal.mul_le_mul_iff_left hÃne hÃtop).mp hchain
      have hgeq : lbf ≤ ⨍⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q ∂volume := by
        rw [hlbf_eq]
        have hpow := ENNReal.rpow_le_rpow hgew hq0.le
        rwa [one_div, ENNReal.rpow_inv_rpow hq0.ne'] at hpow
      rw [setLAverage_eq] at hgeq
      rwa [ENNReal.le_div_iff_mul_le (Or.inl hvol4_ne) (Or.inl hvol4_top)] at hgeq
  -- ============================================================================
  -- SETUP for the assembly: containments, a.e. finiteness, the inner predicate.
  -- ============================================================================
  have hssub16 : Metric.ball x₀ s ⊆ Metric.ball x₀ (16 * R₀) :=
    Metric.ball_subset_ball (by linarith)
  -- `w < ⊤` a.e. on `ball s`.
  have hwfin_ae : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ s)), w z ≠ ⊤ := by
    have h16 : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), w z ^ q ≠ ⊤ :=
      ae_lt_top' (hwmeas.pow_const q).restrict hWfin.ne |>.mono (fun z hz => hz.ne)
    have : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), w z ≠ ⊤ := by
      filter_upwards [h16] with z hz htop
      rw [htop, ENNReal.top_rpow_of_pos hq0] at hz; exact hz rfl
    exact (ae_mono (Measure.restrict_mono hssub16 le_rfl)) this
  -- `b < ⊤` a.e. on `ball s`.
  have hbfin_ae : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ s)), b z ≠ ⊤ := by
    have h16 : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), b z ^ q ≠ ⊤ :=
      ae_lt_top' (hbmeas.pow_const q).restrict hBfin.ne |>.mono (fun z hz => hz.ne)
    have : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (16 * R₀))), b z ≠ ⊤ := by
      filter_upwards [h16] with z hz htop
      rw [htop, ENNReal.top_rpow_of_pos hq0] at hz; exact hz rfl
    exact (ae_mono (Measure.restrict_mono hssub16 le_rfl)) this
  -- The inner predicate: the enlargement `Eᵢ ⊆ ball x₀ s` (engine-able cubes).
  set Inn : Set (ℤ × (ℤ × ℤ)) :=
    {i ∈ B | Metric.ball (cI i) (4 * ρI i) ⊆ Metric.ball x₀ s} with hInndef
  -- The w-good and b-good inner subfamilies.
  set Sw : Set (ℤ × (ℤ × ℤ)) := {i ∈ Inn |
      lwf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), w z} with hSwdef
  set Sb : Set (ℤ × (ℤ × ℤ)) := {i ∈ Inn |
      lbf * volume (Metric.ball (cI i) (4 * ρI i))
        ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), b z ^ q} with hSbdef
  have hSwsub : Sw ⊆ B := fun i hi => hi.1.1
  have hSbsub : Sb ⊆ B := fun i hi => hi.1.1
  have hSwct : Sw.Countable := hBct.mono hSwsub
  have hSbct : Sb.Countable := hBct.mono hSbsub
  -- The localized `u`-weights.
  set uw : ℂ → ℝ≥0∞ := (Metric.ball x₀ s ∩ Esub).indicator w with huwdef
  set ub : ℂ → ℝ≥0∞ := (Metric.ball x₀ s ∩ Fsub).indicator (fun z => b z ^ q) with hubdef
  -- ============================================================================
  -- PER-CUBE ENGINE HYPOTHESES (super-level concentration on inner cubes).
  -- ============================================================================
  have hEsub_nm : NullMeasurableSet Esub volume :=
    nullMeasurableSet_lt aemeasurable_const hwmeas.ennreal_toReal
  have hFsub_nm : NullMeasurableSet Fsub volume :=
    nullMeasurableSet_lt aemeasurable_const hbmeas.ennreal_toReal
  -- w-good inner: `lw·vol(Eᵢ) ≤ ∫_{Eᵢ} uw`.
  have h2uw : ∀ i ∈ Sw, lw * volume (Metric.ball (cI i) (4 * ρI i))
      ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), uw z := by
    rintro i ⟨⟨hiB, hEsub⟩, hwg⟩
    set E : Set ℂ := Metric.ball (cI i) (4 * ρI i) with hEdef
    have hEsubs : E ⊆ Metric.ball x₀ s := hEsub
    have hvolE_top : volume E ≠ ⊤ := measure_ball_lt_top.ne
    -- `∫_E uw = ∫_{E ∩ Esub} w` (since `E ⊆ ball s`).
    have huwint : ∫⁻ z in E, uw z = ∫⁻ z in E ∩ Esub, w z := by
      have hpt : ∀ z ∈ E, uw z = Esub.indicator w z := by
        intro z hz
        rw [huwdef]
        by_cases hzE : z ∈ Esub
        · have hmem : z ∈ Metric.ball x₀ s ∩ Esub := ⟨hEsubs hz, hzE⟩
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzE]
        · have hnmem : z ∉ Metric.ball x₀ s ∩ Esub := fun h => hzE h.2
          rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hzE]
      rw [setLIntegral_congr_fun measurableSet_ball hpt,
        setLIntegral_indicator₀ _
          (hEsub_nm.mono_ac (Measure.restrict_le_self.absolutelyContinuous)),
        Set.inter_comm]
    -- Pointwise a.e. on `E`: `w z ≤ Esub.indicator w z + ofReal(βlam)`.
    have hconc : ∫⁻ z in E, w z
        ≤ (∫⁻ z in E, Esub.indicator w z) + ENNReal.ofReal (β * lam) * volume E := by
      have hstep : ∫⁻ z in E, w z
          ≤ ∫⁻ z in E, (Esub.indicator w z + ENNReal.ofReal (β * lam)) := by
        apply lintegral_mono_ae
        have haef : ∀ᵐ z ∂(volume.restrict E), w z ≠ ⊤ :=
          ae_mono (Measure.restrict_mono hEsubs le_rfl) hwfin_ae
        filter_upwards [haef] with z hzfin
        by_cases hzE : z ∈ Esub
        · rw [Set.indicator_of_mem hzE]; exact le_add_right le_rfl
        · rw [Set.indicator_of_notMem hzE, zero_add]
          rw [hEsubdef, Set.mem_ofPred_eq, not_lt] at hzE
          rw [← ENNReal.ofReal_toReal hzfin]
          exact ENNReal.ofReal_le_ofReal hzE
      rwa [lintegral_add_right' _ aemeasurable_const, setLIntegral_const] at hstep
    have hindint : ∫⁻ z in E, Esub.indicator w z = ∫⁻ z in E ∩ Esub, w z := by
      rw [setLIntegral_indicator₀ _ (hEsub_nm.mono_ac
        (Measure.restrict_le_self.absolutelyContinuous)), Set.inter_comm]
    rw [hindint] at hconc
    -- Combine: `lwf·vol(E) ≤ ∫_E w`, and `lwf = lw + ofReal(βlam)`.
    have hlw_eq : lw + ENNReal.ofReal (β * lam) = lwf := by
      rw [hlwdef, hlwfdef, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      rw [hβdef]; field_simp; ring
    rw [huwint]
    have hkey : lwf * volume E
        ≤ (∫⁻ z in E ∩ Esub, w z) + ENNReal.ofReal (β * lam) * volume E := le_trans hwg hconc
    rw [← hlw_eq, add_mul] at hkey
    refine ENNReal.le_of_add_le_add_right ?_ hkey
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolE_top
  -- b-good inner: `lb·vol(Eᵢ) ≤ ∫_{Eᵢ} ub`.
  have h2ub : ∀ i ∈ Sb, lb * volume (Metric.ball (cI i) (4 * ρI i))
      ≤ ∫⁻ z in Metric.ball (cI i) (4 * ρI i), ub z := by
    rintro i ⟨⟨hiB, hEsub⟩, hbg⟩
    set E : Set ℂ := Metric.ball (cI i) (4 * ρI i) with hEdef
    have hEsubs : E ⊆ Metric.ball x₀ s := hEsub
    have hvolE_top : volume E ≠ ⊤ := measure_ball_lt_top.ne
    have hubint : ∫⁻ z in E, ub z = ∫⁻ z in E ∩ Fsub, b z ^ q := by
      have hpt : ∀ z ∈ E, ub z = Fsub.indicator (fun z => b z ^ q) z := by
        intro z hz
        rw [hubdef]
        by_cases hzF : z ∈ Fsub
        · have hmem : z ∈ Metric.ball x₀ s ∩ Fsub := ⟨hEsubs hz, hzF⟩
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzF]
        · have hnmem : z ∉ Metric.ball x₀ s ∩ Fsub := fun h => hzF h.2
          rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hzF]
      rw [setLIntegral_congr_fun measurableSet_ball hpt,
        setLIntegral_indicator₀ _
          (hFsub_nm.mono_ac (Measure.restrict_le_self.absolutelyContinuous)),
        Set.inter_comm]
    -- Super-level concentration: `bᵠ z ≤ Fsub.indicator bᵠ z + ofReal((βlam)^q)` a.e. on `E`.
    have hconc : ∫⁻ z in E, b z ^ q
        ≤ (∫⁻ z in E, Fsub.indicator (fun z => b z ^ q) z)
          + ENNReal.ofReal ((β * lam) ^ q) * volume E := by
      have hstep : ∫⁻ z in E, b z ^ q
          ≤ ∫⁻ z in E, (Fsub.indicator (fun z => b z ^ q) z + ENNReal.ofReal ((β * lam) ^ q)) := by
        apply lintegral_mono_ae
        have haef : ∀ᵐ z ∂(volume.restrict E), b z ≠ ⊤ :=
          ae_mono (Measure.restrict_mono hEsubs le_rfl) hbfin_ae
        filter_upwards [haef] with z hzfin
        by_cases hzF : z ∈ Fsub
        · rw [Set.indicator_of_mem hzF]; exact le_add_right le_rfl
        · rw [Set.indicator_of_notMem hzF, zero_add]
          rw [hFsubdef, Set.mem_ofPred_eq, not_lt] at hzF
          rw [← ENNReal.ofReal_toReal hzfin,
            ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq0.le]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ENNReal.toReal_nonneg hzF hq0.le)
      rwa [lintegral_add_right' _ aemeasurable_const, setLIntegral_const] at hstep
    have hindint : ∫⁻ z in E, Fsub.indicator (fun z => b z ^ q) z = ∫⁻ z in E ∩ Fsub, b z ^ q := by
      rw [setLIntegral_indicator₀ _ (hFsub_nm.mono_ac
        (Measure.restrict_le_self.absolutelyContinuous)), Set.inter_comm]
    rw [hindint] at hconc
    -- `lb + ofReal((βlam)^q) ≤ lbf` (since `2 ≤ 2^q`).
    have hlb_le : lb + ENNReal.ofReal ((β * lam) ^ q) ≤ lbf := by
      rw [hlbdef, hlbfdef, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h2q : (2:ℝ) ≤ 2 ^ q := by
        calc (2:ℝ) = 2 ^ (1:ℝ) := by rw [Real.rpow_one]
          _ ≤ 2 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hq)
      have hβl : (0:ℝ) ≤ β * lam := by positivity
      have hkey : 2 * (β * lam) ^ q ≤ (lam / (2 * Ã)) ^ q := by
        have heq : lam / (2 * Ã) = 2 * (β * lam) := by rw [hβdef]; field_simp; ring
        rw [heq, Real.mul_rpow (by norm_num) hβl]
        nlinarith [Real.rpow_nonneg hβl q, h2q]
      linarith [hkey]
    rw [hubint]
    have hkey : lbf * volume E
        ≤ (∫⁻ z in E ∩ Fsub, b z ^ q) + ENNReal.ofReal ((β * lam) ^ q) * volume E :=
      le_trans hbg hconc
    have hlbstep : (lb + ENNReal.ofReal ((β * lam) ^ q)) * volume E
        ≤ (∫⁻ z in E ∩ Fsub, b z ^ q) + ENNReal.ofReal ((β * lam) ^ q) * volume E :=
      le_trans (mul_le_mul_left hlb_le _) hkey
    rw [add_mul] at hlbstep
    refine ENNReal.le_of_add_le_add_right ?_ hlbstep
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolE_top
  -- ============================================================================
  -- ENGINE CALLS: bound `vol(⋃_{Sw} Eᵢ)`, `vol(⋃_{Sb} Eᵢ)` by super-level integrals.
  -- ============================================================================
  -- Radius bound: for inner cubes, `4·ρI i ≤ s` (since `Eᵢ ⊆ ball x₀ s`).
  have hRbd : ∀ i ∈ Inn, 4 * ρI i ≤ s := by
    rintro i ⟨hiB, hEsub⟩
    by_contra hgt
    push Not at hgt
    have hvle : volume (Metric.ball (cI i) (4 * ρI i)) ≤ volume (Metric.ball x₀ s) :=
      measure_mono hEsub
    rw [Complex.volume_ball, Complex.volume_ball] at hvle
    have h4ρpos : 0 < 4 * ρI i := by have := hρIpos i; linarith
    rw [ENNReal.mul_le_mul_iff_left (by simp [NNReal.pi_pos.ne']) (by simp)] at hvle
    rw [← ENNReal.ofReal_pow h4ρpos.le, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ s),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvle
    nlinarith [hvle, hgt, h4ρpos]
  have hRbdSw : ∀ i ∈ Sw, 4 * ρI i ≤ s := fun i hi => hRbd i hi.1
  have hRbdSb : ∀ i ∈ Sb, 4 * ρI i ≤ s := fun i hi => hRbd i hi.1
  have hEw := gehring_engine_idx Sw hSwct cI (fun i => 4 * ρI i) lw uw s hRbdSw h2uw
  have hEb := gehring_engine_idx Sb hSbct cI (fun i => 4 * ρI i) lb ub s hRbdSb h2ub
  -- The global integrals of `uw`, `ub` are the super-level masses over `ball x₀ s`.
  have hIuw : ∫⁻ z, uw z = ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z := by
    rw [huwdef, lintegral_indicator₀ (measurableSet_ball.nullMeasurableSet.inter hEsub_nm)]
  have hIub : ∫⁻ z, ub z = ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q := by
    rw [hubdef, lintegral_indicator₀ (measurableSet_ball.nullMeasurableSet.inter hFsub_nm)]
  rw [hIuw] at hEw
  rw [hIub] at hEb
  -- ============================================================================
  -- COLLAR-FREE LHS BOUND.  For `lam ≥ λ₁` every cube `i ∈ B` whose square meets
  -- `ball x₀ t` is INNER (`Eᵢ ⊆ ball x₀ s`), so the LHS super-level mass over
  -- `ball t` is covered by the inner cubes alone: NO boundary collar.
  -- ============================================================================
  set S : Set ℂ := Metric.ball x₀ t ∩ {z : ℂ | lam < (w z).toReal} with hSdef
  have htsub : Metric.ball x₀ t ⊆ Metric.ball x₀ s := Metric.ball_subset_ball hts.le
  -- The finite master mass `Wm = (∫_{16B₀}wᵠ).toReal` and `∫_{ball s}wᵠ ≤ Wm` (ENNReal).
  set Wm : ℝ := (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal with hWmdef
  have hWm0 : 0 ≤ Wm := ENNReal.toReal_nonneg
  have hssub16 : Metric.ball x₀ s ⊆ Metric.ball x₀ (16 * R₀) :=
    Metric.ball_subset_ball (by linarith)
  have hInts_le_Wm : (∫⁻ z in Metric.ball x₀ s, w z ^ q).toReal ≤ Wm := by
    rw [hWmdef]; exact ENNReal.toReal_mono hWfin.ne (lintegral_mono_set hssub16)
  -- KEY: any cube `i ∈ B` meeting `ball x₀ t` is inner.
  have hMeetInn : ∀ i ∈ B, (dyadicSquare i.1 i.2 ∩ Metric.ball x₀ t).Nonempty →
      Metric.ball (cI i) (4 * ρI i) ⊆ Metric.ball x₀ s := by
    intro i hiB hmeet
    obtain ⟨p, hpQ, hpt⟩ := hmeet
    -- `dist x₀ (cI i) ≤ t + ρI i`.
    have hpcI : dist p (cI i) < ρI i := Metric.mem_ball.mp (hQsubball i hpQ)
    have hpx₀ : dist p x₀ < t := Metric.mem_ball.mp hpt
    have hdist : dist x₀ (cI i) ≤ t + ρI i := by
      calc dist x₀ (cI i) ≤ dist x₀ p + dist p (cI i) := dist_triangle _ _ _
        _ = dist p x₀ + dist p (cI i) := by rw [dist_comm x₀ p]
        _ ≤ t + ρI i := by linarith
    -- `ρI i ≤ (s - t)/5`, from `lamᵠ·ρᵢ² ≤ ∫_{ball s}wᵠ ≤ Wm`.
    have hρpos := hρIpos i
    -- `(ofReal lam)^q · vol(Qᵢ) ≤ ∫_{Qᵢ∩ball s}wᵠ ≤ ∫_{ball s}wᵠ`.
    have hQpos : 0 < volume (dyadicSquare i.1 i.2) := by
      rw [volume_dyadicSquare, ENNReal.ofReal_pos]; positivity
    have hQtop : volume (dyadicSquare i.1 i.2) ≠ ⊤ := by
      rw [volume_dyadicSquare]; exact ENNReal.ofReal_ne_top
    have hstop : (ENNReal.ofReal lam) ^ q * volume (dyadicSquare i.1 i.2)
        ≤ ∫⁻ z in dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s, w z ^ q := by
      have h := hBlow i hiB
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl hQpos.ne') (Or.inl hQtop)] at h
      exact h.le
    -- to reals: `lamᵠ · ρᵢ² ≤ Wm`.
    have hInts_fin : ∫⁻ z in dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s, w z ^ q ≠ ⊤ :=
      ne_top_of_le_ne_top hWfin.ne (lintegral_mono_set (Set.inter_subset_right.trans hssub16))
    have hstopR : lam ^ q * (ρI i) ^ 2 ≤ Wm := by
      have hmono := ENNReal.toReal_mono hInts_fin hstop
      have hLHSeq : ((ENNReal.ofReal lam) ^ q * volume (dyadicSquare i.1 i.2)).toReal
          = lam ^ q * (ρI i) ^ 2 := by
        rw [ENNReal.toReal_mul, ENNReal.ofReal_rpow_of_nonneg hlam.le hq0.le,
          ENNReal.toReal_ofReal (by positivity), volume_dyadicSquare,
          ENNReal.toReal_ofReal (by positivity), hρIdef]
      rw [hLHSeq] at hmono
      calc lam ^ q * (ρI i) ^ 2
          ≤ (∫⁻ z in dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s, w z ^ q).toReal := hmono
        _ ≤ Wm := le_trans (ENNReal.toReal_mono hWfin.ne
              (lintegral_mono_set (Set.inter_subset_right.trans hssub16))) le_rfl
    -- `ρᵢ ≤ √Wm / lam^{q/2}`, hence `5ρᵢ ≤ s - t` from `hλ₁`.
    have hlamq2 : 0 < lam ^ (q / 2) := Real.rpow_pos_of_pos hlam _
    have hρWm : ρI i * lam ^ (q / 2) ≤ Real.sqrt Wm := by
      rw [Real.le_sqrt (by positivity) hWm0]
      have hsplit : lam ^ q = (lam ^ (q / 2)) ^ 2 := by
        rw [← Real.rpow_natCast (lam ^ (q/2)) 2, ← Real.rpow_mul hlam.le]
        congr 1; push_cast; ring
      calc (ρI i * lam ^ (q / 2)) ^ 2 = lam ^ q * (ρI i) ^ 2 := by rw [hsplit]; ring
        _ ≤ Wm := hstopR
    have h5ρ : 5 * ρI i ≤ s - t := by
      have hkey : 5 * (ρI i * lam ^ (q / 2)) ≤ (s - t) * lam ^ (q / 2) :=
        le_trans (by linarith [hρWm]) hlam1
      have : 5 * ρI i * lam ^ (q / 2) ≤ (s - t) * lam ^ (q / 2) := by linarith [hkey]
      exact le_of_mul_le_mul_right (by linarith [this]) hlamq2
    -- Conclude `Eᵢ ⊆ ball x₀ s`.
    refine Metric.ball_subset_ball' ?_
    rw [dist_comm]
    linarith [hdist, h5ρ, hρpos]
  -- The inner predicate and the w/b-good subfamilies (same as the core).
  -- `S` is a.e. covered by `⋃_{i∈B} (Qᵢ ∩ ball s)`, but we refine to inner cubes.
  set Cset : ℤ × (ℤ × ℤ) → Set ℂ := fun i => dyadicSquare i.1 i.2 ∩ Metric.ball x₀ s with hCsetdef
  have hCmeas : ∀ i, MeasurableSet (Cset i) :=
    fun i => (measurableSet_dyadicSquare _ _).inter measurableSet_ball
  have hCdisj : B.PairwiseDisjoint Cset := by
    intro i hi j hj hij
    exact (hBdisj hi hj hij).mono Set.inter_subset_left Set.inter_subset_left
  -- a.e. cover of `S` by the INNER cubes: any covering cube meeting `ball t` is inner.
  have hScov : volume (S \ ⋃ i ∈ Inn, Cset i) = 0 := by
    refine measure_mono_null ?_ hBcov
    intro z hz
    obtain ⟨hzS, hznotcov⟩ := hz
    have hzs : z ∈ Metric.ball x₀ s ∩ {z : ℂ | lam < (w z).toReal} :=
      ⟨htsub hzS.1, hzS.2⟩
    refine ⟨hzs, ?_⟩
    intro hzcov
    apply hznotcov
    rw [Set.mem_iUnion₂] at hzcov ⊢
    obtain ⟨i, hi, hzi⟩ := hzcov
    -- `z ∈ Qᵢ` and `z ∈ ball t`, so `Qᵢ` meets `ball t`, hence `i ∈ Inn`.
    have hmeet : (dyadicSquare i.1 i.2 ∩ Metric.ball x₀ t).Nonempty := ⟨z, hzi, hzS.1⟩
    have hiInn : i ∈ Inn := ⟨hi, hMeetInn i hi hmeet⟩
    exact ⟨i, hiInn, hzi, hzs.1⟩
  -- `∫_S wᵠ ≤ ∫_{⋃_{Inn} Cset} wᵠ`.
  have hInnsubB : Inn ⊆ B := fun i hi => hi.1
  have hInnct : Inn.Countable := hBct.mono hInnsubB
  have hUmeasInn : MeasurableSet (⋃ i ∈ Inn, Cset i) :=
    MeasurableSet.biUnion hInnct (fun i _ => hCmeas i)
  have hLHS1 : ∫⁻ z in S, w z ^ q ≤ ∫⁻ z in ⋃ i ∈ Inn, Cset i, w z ^ q := by
    have h1 : (S \ (S \ (⋃ i ∈ Inn, Cset i)) : Set ℂ) =ᵐ[volume] S := sdiff_null_ae_eq_self hScov
    have h2 : S \ (S \ (⋃ i ∈ Inn, Cset i)) = S ∩ (⋃ i ∈ Inn, Cset i) :=
      Set.sdiff_sdiff_right_self S _
    rw [h2] at h1
    rw [setLIntegral_congr h1.symm]
    exact lintegral_mono_set Set.inter_subset_right
  -- INNER BOUND: `∫_{⋃_{Inn} Cset} wᵠ ≤ ofReal(4lamᵠ)·(vol(⋃_{Sw}Eᵢ) + vol(⋃_{Sb}Eᵢ))`.
  have hInnerSum : ∫⁻ z in ⋃ i ∈ Inn, Cset i, w z ^ q
      ≤ ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2) := by
    rw [lintegral_biUnion hInnct (fun i _ => hCmeas i) (hCdisj.subset hInnsubB)]
    calc ∑' i : Inn, ∫⁻ z in Cset i, w z ^ q
        ≤ ∑' i : Inn, ENNReal.ofReal (4 * lam ^ q)
            * volume (dyadicSquare (i : ℤ × (ℤ × ℤ)).1 (i : ℤ × (ℤ × ℤ)).2) := by
          apply ENNReal.tsum_le_tsum
          rintro ⟨i, hi⟩
          exact hBup i (hInnsubB hi)
      _ = ENNReal.ofReal (4 * lam ^ q)
            * ∑' i : Inn, volume (dyadicSquare (i : ℤ × (ℤ × ℤ)).1 (i : ℤ × (ℤ × ℤ)).2) :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2) := by
          rw [measure_biUnion hInnct (Set.Pairwise.mono hInnsubB hBdisj)
            (fun i _ => measurableSet_dyadicSquare _ _)]
  -- `vol(⋃_{Inn} Qᵢ) ≤ vol(⋃_{Sw} Eᵢ) + vol(⋃_{Sb} Eᵢ)`.
  have hQcover : (⋃ i ∈ Inn, dyadicSquare i.1 i.2)
      ⊆ (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
        ∪ (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) := by
    apply Set.iUnion₂_subset
    intro i hi
    have hiB : i ∈ B := hInnsubB hi
    have hQE : dyadicSquare i.1 i.2 ⊆ Metric.ball (cI i) (4 * ρI i) := by
      refine (hQsubball i).trans (Metric.ball_subset_ball ?_)
      have := hρIpos i; linarith
    rcases hdich i hiB with hw | hb
    · have hiSw : i ∈ Sw := ⟨hi, hw⟩
      exact hQE.trans (Set.subset_union_of_subset_left
        (Set.subset_biUnion_of_mem (u := fun i => Metric.ball (cI i) (4 * ρI i)) hiSw) _)
    · have hiSb : i ∈ Sb := ⟨hi, hb⟩
      exact hQE.trans (Set.subset_union_of_subset_right
        (Set.subset_biUnion_of_mem (u := fun i => Metric.ball (cI i) (4 * ρI i)) hiSb) _)
  have hQvol : volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2)
      ≤ volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
        + volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) :=
    le_trans (measure_mono hQcover) (measure_union_le _ _)
  -- COEFFICIENT TRANSFER (identical to the core).
  set Cw : ℝ := 256 * Ã * lam ^ (q - 1) with hCwdef
  set Cb : ℝ := 64 * (4 * Ã) ^ q with hCbdef
  have hlw_ne : lw ≠ 0 := by rw [hlwdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hlb_ne : lb ≠ 0 := by rw [hlbdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hlw_top : lw ≠ ⊤ := by rw [hlwdef]; exact ENNReal.ofReal_ne_top
  have hlb_top : lb ≠ ⊤ := by rw [hlbdef]; exact ENNReal.ofReal_ne_top
  have hlamq : lam ^ (q - 1) * lam = lam ^ q := by
    have h := (Real.rpow_add hlam (q - 1) 1).symm
    rw [Real.rpow_one] at h
    rw [h]; congr 1; ring
  have hCw_mul : ENNReal.ofReal Cw * lw = 16 * ENNReal.ofReal (4 * lam ^ q) := by
    rw [hCwdef, hlwdef, ← ENNReal.ofReal_mul (by positivity),
      show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by rw [ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [hβdef]
    have : 256 * Ã * lam ^ (q - 1) * (1 / (4 * Ã) * lam) = 64 * (lam ^ (q - 1) * lam) := by
      field_simp; ring
    rw [this, hlamq]; ring
  have hCb_mul : ENNReal.ofReal Cb * lb = 16 * ENNReal.ofReal (4 * lam ^ q) := by
    rw [hCbdef, hlbdef, ← ENNReal.ofReal_mul (by positivity),
      show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by rw [ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    have hbase : (4 * Ã) * (β * lam) = lam := by rw [hβdef]; field_simp
    have hmr : (4 * Ã) ^ q * (β * lam) ^ q = lam ^ q := by
      rw [← Real.mul_rpow (by positivity) (by positivity [hβpos]), hbase]
    rw [show (64 * (4 * Ã) ^ q * (β * lam) ^ q : ℝ) = 64 * ((4 * Ã) ^ q * (β * lam) ^ q) by ring,
      hmr]; ring
  have hsixteen_ne : (16 : ℝ≥0∞) ≠ 0 := by norm_num
  have hsixteen_top : (16 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hTransW : ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
      ≤ ENNReal.ofReal Cw * ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z := by
    apply (ENNReal.mul_le_mul_iff_right hsixteen_ne hsixteen_top).mp
    calc (16 : ℝ≥0∞) * (ENNReal.ofReal (4 * lam ^ q)
            * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i)))
        = (ENNReal.ofReal Cw * lw) * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i)) := by
          rw [hCw_mul]; ring
      _ = ENNReal.ofReal Cw * (lw * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))) := by ring
      _ ≤ ENNReal.ofReal Cw * (16 * ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z) :=
          mul_le_mul_right hEw _
      _ = 16 * (ENNReal.ofReal Cw * ∫⁻ z in Metric.ball x₀ s ∩ Esub, w z) := by ring
  have hTransB : ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i))
      ≤ ENNReal.ofReal Cb * ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q := by
    apply (ENNReal.mul_le_mul_iff_right hsixteen_ne hsixteen_top).mp
    calc (16 : ℝ≥0∞) * (ENNReal.ofReal (4 * lam ^ q)
            * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)))
        = (ENNReal.ofReal Cb * lb) * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) := by
          rw [hCb_mul]; ring
      _ = ENNReal.ofReal Cb * (lb * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i))) := by ring
      _ ≤ ENNReal.ofReal Cb * (16 * ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q) :=
          mul_le_mul_right hEb _
      _ = 16 * (ENNReal.ofReal Cb * ∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q) := by ring
  -- FINAL COMBINATION (collar-free).
  have hβeq : (1 : ℝ) / (4 * (Real.pi ^ (1 / q) * A + 1)) = β := by
    rw [hβdef, hÃdef, hPdef]
  have hCw_goal : (256 : ℝ) * (Real.pi ^ (1 / q) * A + 1) * lam ^ (q - 1) = Cw := by
    rw [hCwdef, hÃdef, hPdef]
  have hCb_goal : (64 : ℝ) * (4 * (Real.pi ^ (1 / q) * A + 1)) ^ q = Cb := by
    rw [hCbdef, hÃdef, hPdef]
  have hgoal : ∫⁻ z in S, w z ^ q
      ≤ ENNReal.ofReal Cw * (∫⁻ z in Metric.ball x₀ s ∩ Esub, w z)
          + ENNReal.ofReal Cb * (∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q) :=
    calc ∫⁻ z in S, w z ^ q
        ≤ ∫⁻ z in ⋃ i ∈ Inn, Cset i, w z ^ q := hLHS1
      _ ≤ ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Inn, dyadicSquare i.1 i.2) := hInnerSum
      _ ≤ ENNReal.ofReal (4 * lam ^ q)
              * (volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
                + volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i))) := mul_le_mul_right hQvol _
      _ = ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sw, Metric.ball (cI i) (4 * ρI i))
            + ENNReal.ofReal (4 * lam ^ q) * volume (⋃ i ∈ Sb, Metric.ball (cI i) (4 * ρI i)) := by
          rw [mul_add]
      _ ≤ ENNReal.ofReal Cw * (∫⁻ z in Metric.ball x₀ s ∩ Esub, w z)
            + ENNReal.ofReal Cb * (∫⁻ z in Metric.ball x₀ s ∩ Fsub, b z ^ q) :=
          add_le_add hTransW hTransB
  exact hgoal


/-! ## Hole-filling pillars for `gehring_selfImprovement` (STEP B).

The `O(ε)` Gehring gain decomposes ONLY the `w^ε` factor, KEEPING the `w^q` mass:
`∫ f^{q+ε} = ε·∫_{λ>0} λ^{ε-1}·(∫_{{f>λ}} f^q) dλ`.  The leading `ε` is the gain.
These private helpers prove: the `w^ε`-mass layer-cake (`gehring_mass_layerCake`), its
Tonelli reconstruction (`gehring_recon`), the ε-absorption assembly (`gehring_assembly`),
the `.toReal` conversion (`gehring_toReal_conv`), and the hole-fill packaging
(`gehring_holeFill`) consuming the truncated super-level good-λ. -/

private theorem gehring_scalar_lc (c : ℝ) (hc : 0 ≤ c) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ lam in Set.Ioo (0:ℝ) c, ENNReal.ofReal (lam ^ (ε - 1)) = ENNReal.ofReal (c ^ ε / ε) := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · subst hc0; simp [Real.zero_rpow hε.ne']
  · have hii : IntervalIntegrable (fun lam => lam ^ (ε - 1)) volume 0 c :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ) < ε - 1)
    have hint : IntegrableOn (fun lam => lam ^ (ε - 1)) (Set.Ioo 0 c) volume := by
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hcpos.le).mp hii
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo 0 c)] (fun lam => lam ^ (ε - 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with lam hlam
      exact Real.rpow_nonneg hlam.1.le _
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hcpos.le]
    rw [integral_rpow (Or.inl (by linarith : (-1:ℝ) < ε - 1))]
    rw [Real.zero_rpow (by linarith : ε - 1 + 1 ≠ 0)]
    rw [show ε - 1 + 1 = ε by ring]; ring


/-- **`Ž_N`-layer-cake (`q`-mass × truncated `ε`-factor).**  The iterated quantity of
STEP B is `Ž_N(t) = ∫_{ball t} w^q · (min w N)^ε` (the FULL `q`-mass `w^q` times the
TRUNCATED `ε`-gain factor `(min w N)^ε`).  Its `(min w N).toReal`-layer-cake decomposes ONLY the
bounded `ε`-factor (`min w N ≤ N`, so the `λ`-integral lives on `(0,N)`) while keeping the full,
a-priori-integrable `w^q` mass.  This is the device that eliminates the over-truncation tail: the
inner super-level integral is the FULL `∫_{{w>λ}} w^q` (not the truncated `(min w N)^q`-mass), so
the good-λ that feeds it is the honest exponent-preserving one for the integrable `w^q`. -/
private theorem gehring_mass_layerCake {q ε : ℝ} (_hq0 : 0 < q) (hε : 0 < ε) {w : ℂ → ℝ≥0∞}
    (hwmeas : AEMeasurable w volume) (N : ℕ) (x₀ : ℂ) (t : ℝ) :
    ∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
      = ENNReal.ofReal ε * ∫⁻ lam in Set.Ioi (0:ℝ),
          (∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal},
            w z ^ q) * ENNReal.ofReal (lam ^ (ε - 1)) := by
  classical
  set f : ℂ → ℝ≥0∞ := fun z => min (w z) (N : ℝ≥0∞) with hfdef
  have hfmeas : AEMeasurable f volume := hwmeas.min aemeasurable_const
  have hffin : ∀ z, f z ≠ ⊤ := fun z =>
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
  set μ : Measure ℂ :=
    (volume.restrict (Metric.ball x₀ t)).withDensity (fun z => w z ^ q) with hμdef
  have hwqmeas : AEMeasurable (fun z => w z ^ q) (volume.restrict (Metric.ball x₀ t)) :=
    (hwmeas.restrict).pow_const q
  have hLHS : ∫⁻ z in Metric.ball x₀ t, w z ^ q * f z ^ ε = ∫⁻ z, f z ^ ε ∂μ := by
    rw [hμdef, lintegral_withDensity_eq_lintegral_mul₀ hwqmeas ((hfmeas.restrict).pow_const ε)]
    apply lintegral_congr_ae
    filter_upwards with z
    simp only [Pi.mul_apply]
  rw [hLHS]
  set g : ℂ → ℝ := fun z => (f z).toReal with hgdef
  have hpt : ∀ z, f z ^ ε = ENNReal.ofReal (g z ^ ε) := by
    intro z
    rw [hgdef, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hε.le,
      ENNReal.ofReal_toReal (hffin z)]
  have hgnn : 0 ≤ᵐ[μ] g := Filter.Eventually.of_forall (fun z => ENNReal.toReal_nonneg)
  have hgmeas : AEMeasurable g μ := by
    refine (hfmeas.ennreal_toReal.restrict (s := Metric.ball x₀ t)).mono' ?_
    rw [hμdef]; exact withDensity_absolutelyContinuous _ _
  have hrpowlc := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := μ) hgnn hgmeas hε
  rw [show (∫⁻ z, f z ^ ε ∂μ) = ∫⁻ z, ENNReal.ofReal (g z ^ ε) ∂μ from lintegral_congr hpt]
  rw [hrpowlc]
  congr 1
  apply lintegral_congr
  intro lam
  congr 1
  have hwqvol : AEMeasurable (fun z => w z ^ q) volume := hwmeas.pow_const q
  have hgvol : AEMeasurable g volume := hfmeas.ennreal_toReal
  have hmslt : NullMeasurableSet {a : ℂ | lam < g a} (volume.restrict (Metric.ball x₀ t)) :=
    nullMeasurableSet_lt aemeasurable_const hgvol.restrict
  rw [hμdef, withDensity_apply₀ _ hmslt, Measure.restrict_restrict₀ hmslt]
  have hseteq : {a : ℂ | lam < g a} ∩ Metric.ball x₀ t
      = Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal} := by
    rw [hgdef]; ext z; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
  rw [hseteq]

private theorem gehring_recon {p β : ℝ} (hp : 0 < p) (hβ : 0 < β) {D : ℂ → ℝ≥0∞} {θ : ℂ → ℝ}
    (hDmeas : AEMeasurable D volume) (hθmeas : AEMeasurable θ volume)
    (hθnn : ∀ z, 0 ≤ θ z) (x₀ : ℂ) (s : ℝ) :
    ∫⁻ lam in Set.Ioi (0:ℝ),
        (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < θ z}, D z)
          * ENNReal.ofReal (lam ^ (p - 1))
      = ENNReal.ofReal (1 / (p * β ^ p)) *
          ∫⁻ z in Metric.ball x₀ s, D z * ENNReal.ofReal (θ z ^ p) := by
  classical
  set ν : Measure ℂ := (volume.restrict (Metric.ball x₀ s)).withDensity D with hνdef
  have hinner : ∀ lam : ℝ, (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < θ z}, D z)
      = ν {z | β * lam < θ z} := by
    intro lam
    have hmslt : NullMeasurableSet {z : ℂ | β * lam < θ z} (volume.restrict (Metric.ball x₀ s)) :=
      nullMeasurableSet_lt aemeasurable_const hθmeas.restrict
    rw [hνdef, withDensity_apply₀ _ hmslt, Measure.restrict_restrict₀ hmslt]
    have hseteq : {z : ℂ | β * lam < θ z} ∩ Metric.ball x₀ s
        = Metric.ball x₀ s ∩ {z | β * lam < θ z} := Set.inter_comm _ _
    rw [hseteq]
  simp_rw [hinner]
  set hθ : ℂ → ℝ := fun z => θ z / β with hθdef
  have hνset : ∀ lam : ℝ, ν {z | β * lam < θ z} = ν {z | lam < hθ z} := by
    intro lam; congr 1; ext z
    simp only [Set.mem_ofPred_eq, hθdef, lt_div_iff₀ hβ, mul_comm]
  simp_rw [hνset]
  have hhnn : 0 ≤ᵐ[ν] hθ := Filter.Eventually.of_forall (fun z => by
    rw [hθdef]; exact div_nonneg (hθnn z) hβ.le)
  have hhmeas : AEMeasurable hθ ν := by
    have h1 : AEMeasurable hθ (volume.restrict (Metric.ball x₀ s)) := by
      rw [hθdef]; exact hθmeas.restrict.div_const β
    refine h1.mono' ?_
    rw [hνdef]; exact withDensity_absolutelyContinuous _ _
  have hlc := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := ν) hhnn hhmeas hp
  have hdens : ∫⁻ z, ENNReal.ofReal (hθ z ^ p) ∂ν
      = ENNReal.ofReal (1 / β ^ p) * ∫⁻ z in Metric.ball x₀ s, D z * ENNReal.ofReal (θ z ^ p) := by
    rw [hνdef, lintegral_withDensity_eq_lintegral_mul₀ hDmeas.restrict
        (by
          refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
          have hhr : AEMeasurable hθ (volume.restrict (Metric.ball x₀ s)) := by
            rw [hθdef]; exact hθmeas.restrict.div_const β
          exact hhr.pow_const p)]
    rw [← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top : ENNReal.ofReal (1 / β ^ p) ≠ ⊤)]
    apply lintegral_congr_ae
    filter_upwards with z
    simp only [Pi.mul_apply, hθdef]
    rw [Real.div_rpow (hθnn z) hβ.le, ENNReal.ofReal_div_of_pos (by positivity)]
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ) < β ^ p), div_eq_mul_inv]
    ring
  rw [hdens] at hlc
  have hp0 : ENNReal.ofReal p ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eq_comm, ← ENNReal.eq_div_iff hp0 hptop] at hlc
  rw [hlc, ENNReal.div_eq_inv_mul]
  rw [show ENNReal.ofReal (1 / (p * β ^ p))
      = (ENNReal.ofReal p)⁻¹ * ENNReal.ofReal (1 / β ^ p) from ?_]
  · ring
  · rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp


/-- **The crux pointwise inequality.**  For `w : ℝ≥0∞`, `N : ℕ`, `1 < q`, `0 ≤ ε`,
`w · (min w N).toReal^{q+ε-1} ≤ w^q · (min w N)^ε`.  This is the inequality that eliminates the
over-truncation tail: on `{w ≤ N}` it is an equality (`w·w^{q+ε-1} = w^{q+ε} = w^q·w^ε`); on
`{w > N}` (`min w N = N`) it reads `w·N^{q+ε-1} ≤ w^q·N^ε`, i.e. `N^{q-1} ≤ w^{q-1}`, true since
`w > N` and `q-1 ≥ 0`.  It is what makes the reconstruction of the honest exponent-1 good-λ land
in the FINITE truncated quantity `Ž_N = ∫ w^q (min w N)^ε` rather than the untruncated energy. -/
private theorem gehring_crux_le {q ε : ℝ} (hq : 1 < q) (hε : 0 ≤ ε) (w : ℝ≥0∞) (N : ℕ) :
    w * ENNReal.ofReal ((min w (N : ℝ≥0∞)).toReal ^ (q + ε - 1))
      ≤ w ^ q * (min w (N : ℝ≥0∞)) ^ ε := by
  have hq0 : (0:ℝ) < q := lt_trans one_pos hq
  have hqε1 : (0:ℝ) ≤ q + ε - 1 := by linarith
  have hminfin : min w (N : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
  rcases le_total w (N : ℝ≥0∞) with hwN | hwN
  · -- `w ≤ N`: `min w N = w`.  Equality `w·w^{q+ε-1} = w^q·w^ε`.
    have hmin : min w (N : ℝ≥0∞) = w := min_eq_left hwN
    rw [hmin]
    rcases eq_or_ne w ⊤ with hwtop | hwfin
    · exact absurd (hwtop ▸ hwN) (by simp)
    · rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hqε1, ENNReal.ofReal_toReal hwfin]
      rw [show w * w ^ (q + ε - 1) = w ^ (1:ℝ) * w ^ (q + ε - 1) by rw [ENNReal.rpow_one]]
      rw [← ENNReal.rpow_add_of_nonneg (1:ℝ) (q + ε - 1) zero_le_one hqε1]
      rw [← ENNReal.rpow_add_of_nonneg q ε hq0.le hε]
      rw [show (1:ℝ) + (q + ε - 1) = q + ε by ring]
  · -- `w ≥ N`: `min w N = N`.  Need `w·N^{q+ε-1} ≤ w^q·N^ε`, i.e. `w·N^{q-1} ≤ w^q`.
    have hmin : min w (N : ℝ≥0∞) = (N : ℝ≥0∞) := min_eq_right hwN
    rw [hmin]
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · -- `N = 0`: `min = 0`, `(0).toReal = 0`, LHS = `w·ofReal(0^{q+ε-1}) = 0` (since `q+ε-1>0`).
      subst hN0
      simp only [Nat.cast_zero, ENNReal.toReal_zero]
      rw [Real.zero_rpow (by linarith : q + ε - 1 ≠ 0), ENNReal.ofReal_zero, mul_zero]
      exact zero_le
    · have hNreal : ((N:ℝ≥0∞)).toReal = (N:ℝ) := by simp
      rw [hNreal]
      -- RHS factor `(N:ℝ≥0∞)^ε = ofReal((N:ℝ)^ε)`.
      have hNε : (N:ℝ≥0∞) ^ ε = ENNReal.ofReal ((N:ℝ) ^ ε) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg N) hε]
      rw [hNε]
      -- LHS = w·ofReal(N^{q+ε-1}) = w·ofReal(N^{q-1})·ofReal(N^ε).
      rw [show (N:ℝ) ^ (q + ε - 1) = (N:ℝ) ^ (q - 1) * (N:ℝ) ^ ε by
        rw [← Real.rpow_add (by exact_mod_cast hNpos)]; ring_nf]
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [show w * (ENNReal.ofReal ((N:ℝ)^(q-1)) * ENNReal.ofReal ((N:ℝ)^ε))
        = (w * ENNReal.ofReal ((N:ℝ)^(q-1))) * ENNReal.ofReal ((N:ℝ)^ε) by ring]
      apply mul_le_mul_left
      -- `w·N^{q-1} ≤ w^q`.  Since `N ≤ w`: `N^{q-1} ≤ w^{q-1}`, and `w·w^{q-1}=w^q`.
      have hNlew : (ENNReal.ofReal ((N:ℝ)^(q-1))) ≤ w ^ (q - 1) := by
        rw [← ENNReal.ofReal_natCast (n := N)] at hwN
        calc ENNReal.ofReal ((N:ℝ)^(q-1))
            = (ENNReal.ofReal (N:ℝ)) ^ (q - 1) := by
              rw [← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg N) (by linarith)]
          _ ≤ w ^ (q - 1) := ENNReal.rpow_le_rpow hwN (by linarith)
      calc w * ENNReal.ofReal ((N:ℝ)^(q-1)) ≤ w * w ^ (q - 1) := mul_le_mul_right hNlew _
        _ = w ^ (1:ℝ) * w ^ (q - 1) := by rw [ENNReal.rpow_one]
        _ = w ^ (q:ℝ) := by
            rw [← ENNReal.rpow_add_of_nonneg (1:ℝ) (q-1) zero_le_one (by linarith),
              show (1:ℝ) + (q - 1) = q by ring]

private theorem gehring_assembly {q A ε : ℝ} (hq : 1 < q) (_hA : 0 ≤ A) (hεpos : 0 < ε)
    (_hεle : ε ≤ 1)
    {w b : ℂ → ℝ≥0∞} (hwmeas : AEMeasurable w volume) (hbmeas : AEMeasurable b volume)
    (x₀ : ℂ) (R₀ : ℝ) (_hR₀ : 0 < R₀)
    (Cw Cb β : ℝ) (hCw : 0 ≤ Cw) (hCb : 0 ≤ Cb) (hβ0 : 0 < β) (_hβ1 : β < 1)
    (N : ℕ) (t s : ℝ) (_ht : 4 * R₀ ≤ t) (_hts : t < s) (_hs : s ≤ 16 * R₀)
    -- THRESHOLD SPLIT.  The good-λ is consumed only on the HIGH range `lam ≥ lam₀`; on the LOW
    -- range `0 < lam < lam₀` the super-level `w^q`-mass is bounded by the master mass `Wlow`.
    (lam₀ : ℝ) (hlam₀0 : 0 ≤ lam₀) (Wlow : ℝ≥0∞) (hWlowtop : Wlow ≠ ⊤)
    (hWlow : ∀ lam : ℝ, 0 < lam →
      ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q ≤ Wlow)
    -- The honest exponent-1 good-λ (TRUNCATED super-level on the RHS w-mass, FULL `w^q` on LHS),
    -- valid on the HIGH range `lam ≥ lam₀`:
    (hGL : ∀ lam : ℝ, 0 < lam → lam₀ ≤ lam →
      ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q
        ≤ ENNReal.ofReal (Cw * lam ^ (q - 1))
            * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
          + ENNReal.ofReal Cb
            * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q)) :
    ∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
      ≤ ENNReal.ofReal (lam₀ ^ ε) * Wlow
        + (ENNReal.ofReal (Cw / ((q + ε - 1) * β ^ (q + ε - 1)) * ε)
          * (∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε)
        + ENNReal.ofReal (Cb / β ^ ε) * (∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε))) := by
  classical
  have hq0 : 0 < q := lt_trans one_pos hq
  have hqε1 : 0 < q + ε - 1 := by linarith
  -- Step 1: layer-cake LHS.
  rw [gehring_mass_layerCake hq0 hεpos hwmeas N x₀ t]
  -- Step 2: THRESHOLD SPLIT of the λ-integral `Ioi 0 = Ioo 0 lam₀ ∪ Ici lam₀`.
  -- Abbreviations for the inner super-level integral and the good-λ RHS integrand.
  set Inner : ℝ → ℝ≥0∞ := fun lam =>
    ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q with hInnerdef
  set GLrhs : ℝ → ℝ≥0∞ := fun lam =>
    ENNReal.ofReal (Cw * lam ^ (q - 1))
        * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
      + ENNReal.ofReal Cb
        * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q) with hGLrhsdef
  -- Measurability of `Inner` (antitone level integral) for the set-split lemma.
  have hInner_meas : Measurable Inner := by
    have hanti : Antitone Inner := by
      intro a c hac; apply lintegral_mono_set; intro z hz
      exact ⟨hz.1, lt_of_le_of_lt hac hz.2⟩
    exact hanti.measurable
  have hgw_meas : Measurable (fun lam : ℝ => ENNReal.ofReal (lam ^ (ε - 1))) := by
    apply ENNReal.measurable_ofReal.comp; fun_prop
  -- The split bound: `∫_{Ioi 0} Inner·g ≤ LOW + HIGH` where LOW = `Wlow·lam₀^ε/ε` (as a λ-integral
  -- over `Ioo 0 lam₀`) and HIGH = `∫_{Ioi 0} GLrhs·g` (the good-λ RHS over all of `Ioi 0`,
  -- which dominates the `Ici lam₀` part by nonnegativity).
  have hsplit : ∫⁻ lam in Set.Ioi (0:ℝ), Inner lam * ENNReal.ofReal (lam ^ (ε - 1))
      ≤ (∫⁻ lam in Set.Ioo (0:ℝ) lam₀, Wlow * ENNReal.ofReal (lam ^ (ε - 1)))
        + ∫⁻ lam in Set.Ioi (0:ℝ), GLrhs lam * ENNReal.ofReal (lam ^ (ε - 1)) := by
    rcases eq_or_lt_of_le hlam₀0 with hlam₀eq | hlam₀pos
    · -- `lam₀ = 0`: the LOW range `Ioo 0 0` is empty; HIGH covers everything.
      subst hlam₀eq
      simp only [Set.Ioo_self, Measure.restrict_empty, lintegral_zero_measure, zero_add]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with lam hlam
      exact mul_le_mul_left (hGL lam hlam (le_of_lt hlam)) _
    · -- `lam₀ > 0`: split `Ioi 0 = Ioo 0 lam₀ ∪ Ici lam₀`.
      have hunion : Set.Ioi (0:ℝ) = Set.Ioo (0:ℝ) lam₀ ∪ Set.Ici lam₀ :=
        (Set.Ioo_union_Ici_eq_Ioi hlam₀pos).symm
      have hLHSsplit : ∫⁻ lam in Set.Ioi (0:ℝ), Inner lam * ENNReal.ofReal (lam ^ (ε - 1))
          = (∫⁻ lam in Set.Ioo (0:ℝ) lam₀, Inner lam * ENNReal.ofReal (lam ^ (ε - 1)))
            + ∫⁻ lam in Set.Ici lam₀, Inner lam * ENNReal.ofReal (lam ^ (ε - 1)) := by
        rw [hunion, lintegral_union measurableSet_Ici
          (Set.disjoint_left.mpr (fun lam h1 h2 => absurd h2 (not_le.mpr h1.2)))]
      rw [hLHSsplit]
      apply add_le_add
      · -- LOW: `Inner lam ≤ Wlow` on `Ioo 0 lam₀`.
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with lam hlam
        exact mul_le_mul_left (hWlow lam hlam.1) _
      · -- HIGH: `Inner lam ≤ GLrhs lam` on `Ici lam₀ ⊆ {lam ≥ lam₀, lam > 0}`, then extend to
        -- `Ioi 0`.
        calc ∫⁻ lam in Set.Ici lam₀, Inner lam * ENNReal.ofReal (lam ^ (ε - 1))
            ≤ ∫⁻ lam in Set.Ici lam₀, GLrhs lam * ENNReal.ofReal (lam ^ (ε - 1)) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ici] with lam hlam
              exact mul_le_mul_left (hGL lam (lt_of_lt_of_le hlam₀pos hlam) hlam) _
          _ ≤ ∫⁻ lam in Set.Ioi (0:ℝ), GLrhs lam * ENNReal.ofReal (lam ^ (ε - 1)) := by
              apply lintegral_mono_set
              exact fun lam hlam => lt_of_lt_of_le hlam₀pos hlam
  -- Bound the LOW λ-integral via `gehring_scalar_lc`.
  have hlow_eval : ∫⁻ lam in Set.Ioo (0:ℝ) lam₀, Wlow * ENNReal.ofReal (lam ^ (ε - 1))
      = Wlow * ENNReal.ofReal (lam₀ ^ ε / ε) := by
    rw [lintegral_const_mul' _ _ hWlowtop, gehring_scalar_lc lam₀ hlam₀0 ε hεpos]
  rw [hlow_eval] at hsplit
  -- Assemble: `Ž_N(t) = ε·∫_{Ioi 0} Inner·g ≤ ε·(LOW + HIGH)`.
  rw [show (∫⁻ lam in Set.Ioi (0:ℝ), Inner lam * ENNReal.ofReal (lam ^ (ε - 1)))
      = ∫⁻ lam in Set.Ioi (0:ℝ),
        (∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q)
          * ENNReal.ofReal (lam ^ (ε - 1)) from rfl]
  refine le_trans (mul_le_mul_right hsplit _) ?_
  rw [mul_add]
  apply add_le_add
  · -- `ε·(Wlow·lam₀^ε/ε) = ofReal(lam₀^ε)·Wlow`.
    rw [← mul_assoc, mul_comm (ENNReal.ofReal ε) Wlow, mul_assoc]
    apply le_of_eq
    rw [show ENNReal.ofReal ε * ENNReal.ofReal (lam₀ ^ ε / ε) = ENNReal.ofReal (lam₀ ^ ε) from by
      rw [← ENNReal.ofReal_mul hεpos.le]
      congr 1; field_simp]
    ring
  -- HIGH part: the existing reconstruction (identical to the previous assembly proof).
  simp only [hGLrhsdef]
  -- Distribute (A+B)*g into A*g + B*g pointwise on Ioi 0, then split the integral.
  have hpw : ∀ lam : ℝ, lam ∈ Set.Ioi (0:ℝ) →
      (ENNReal.ofReal (Cw * lam ^ (q - 1))
          * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
        + ENNReal.ofReal Cb
          * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q))
        * ENNReal.ofReal (lam ^ (ε - 1))
      = ENNReal.ofReal Cw *
            ((∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
              * ENNReal.ofReal (lam ^ ((q + ε - 1) - 1)))
        + ENNReal.ofReal Cb *
            ((∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q)
              * ENNReal.ofReal (lam ^ (ε - 1))) := by
    intro lam hlam
    have hlampos : 0 < lam := hlam
    rw [add_mul]
    congr 1
    · rw [show ENNReal.ofReal (Cw * lam ^ (q - 1))
              = ENNReal.ofReal Cw * ENNReal.ofReal (lam ^ (q - 1)) from by
            rw [← ENNReal.ofReal_mul hCw]]
      rw [show (q + ε - 1) - 1 = (q - 1) + (ε - 1) by ring]
      rw [Real.rpow_add hlampos, ENNReal.ofReal_mul (Real.rpow_nonneg hlampos.le _)]
      ring
    · ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpw]
  -- Split the integral.
  rw [lintegral_add_left' ?_]
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    -- w-term reconstruction: `θ := (min w N).toReal` (TRUNCATED level), `D := w` (FULL integrand).
    rw [gehring_recon hqε1 hβ0 hwmeas (hwmeas.min aemeasurable_const).ennreal_toReal
          (fun z => ENNReal.toReal_nonneg) x₀ s]
    rw [gehring_recon hεpos hβ0 (hbmeas.pow_const q) hbmeas.ennreal_toReal
          (fun z => ENNReal.toReal_nonneg) x₀ s]
    -- The crux comparison: `∫ w·ofReal((min w N).toReal^{q+ε-1}) ≤ ∫ w^q·(min w N)^ε = Ž_N(s)`.
    have hwid : ∫⁻ z in Metric.ball x₀ s,
          w z * ENNReal.ofReal ((min (w z) (N:ℝ≥0∞)).toReal ^ (q + ε - 1))
        ≤ ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε := by
      apply lintegral_mono
      intro z
      exact gehring_crux_le hq hεpos.le (w z) N
    have hbid : ∫⁻ z in Metric.ball x₀ s, b z ^ q * ENNReal.ofReal ((b z).toReal ^ ε)
        ≤ ∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε) := by
      apply lintegral_mono_ae
      filter_upwards with z
      rcases eq_or_ne (b z) ⊤ with hbtop | hbfin
      · rw [hbtop]
        simp only [ENNReal.toReal_top, Real.zero_rpow hεpos.ne', ENNReal.ofReal_zero, mul_zero]
        exact zero_le
      · rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hεpos.le,
          ENNReal.ofReal_toReal hbfin]
        rw [← ENNReal.rpow_add_of_nonneg q ε hq0.le hεpos.le]
    calc ENNReal.ofReal ε *
            (ENNReal.ofReal Cw * (ENNReal.ofReal (1 / ((q + ε - 1) * β ^ (q + ε - 1)))
                * ∫⁻ z in Metric.ball x₀ s,
                    w z * ENNReal.ofReal ((min (w z) (N:ℝ≥0∞)).toReal ^ (q + ε - 1)))
              + ENNReal.ofReal Cb * (ENNReal.ofReal (1 / (ε * β ^ ε))
                * ∫⁻ z in Metric.ball x₀ s, b z ^ q * ENNReal.ofReal ((b z).toReal ^ ε)))
        ≤ ENNReal.ofReal ε *
            (ENNReal.ofReal Cw * (ENNReal.ofReal (1 / ((q + ε - 1) * β ^ (q + ε - 1)))
                * ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε)
              + ENNReal.ofReal Cb * (ENNReal.ofReal (1 / (ε * β ^ ε))
                * ∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε))) := by gcongr
      _ = ENNReal.ofReal (Cw / ((q + ε - 1) * β ^ (q + ε - 1)) * ε)
              * (∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε)
            + ENNReal.ofReal (Cb / β ^ ε) * (∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε)) := by
          have triple : ∀ (a bb c : ℝ) (I : ℝ≥0∞), 0 ≤ a → 0 ≤ bb →
              ENNReal.ofReal a * (ENNReal.ofReal bb * (ENNReal.ofReal c * I))
                = ENNReal.ofReal (a * bb * c) * I := by
            intro a bb c I ha hb
            rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul ha,
              ← ENNReal.ofReal_mul (by positivity)]
          rw [mul_add, triple ε Cw _ _ hεpos.le hCw, triple ε Cb _ _ hεpos.le hCb]
          have e1 : ε * Cw * (1 / ((q + ε - 1) * β ^ (q + ε - 1)))
              = Cw / ((q + ε - 1) * β ^ (q + ε - 1)) * ε := by ring
          have e2 : ε * Cb * (1 / (ε * β ^ ε)) = Cb / β ^ ε := by
            rw [eq_div_iff (by positivity : β ^ ε ≠ 0)]; field_simp
          rw [e1, e2]
  · -- AEMeasurable of the w-summand: (antitone level-integral) * ofReal(λ^{p-1}).
    have hanti : Antitone (fun lam : ℝ =>
        ∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z) := by
      intro a c hac
      apply lintegral_mono_set
      intro z hz
      refine ⟨hz.1, ?_⟩
      have hmul : β * a ≤ β * c := mul_le_mul_of_nonneg_left hac hβ0.le
      exact lt_of_le_of_lt hmul hz.2
    have hmeas1 : Measurable (fun lam : ℝ =>
        ∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z) :=
      hanti.measurable
    have hmeasrpow : Measurable (fun lam : ℝ => ENNReal.ofReal (lam ^ ((q + ε - 1) - 1))) := by
      apply ENNReal.measurable_ofReal.comp; fun_prop
    exact ((measurable_const.mul (hmeas1.mul hmeasrpow)).aemeasurable).restrict

private theorem gehring_toReal_conv {q κ κ' ε Cb β : ℝ} {w b : ℂ → ℝ≥0∞} {x₀ : ℂ}
    {Wmaster Bmaster t s : ℝ}
    (N : ℕ)
    (hκ'κ : κ' ≤ κ) (hκ'0 : 0 ≤ κ') (hε0 : 0 ≤ ε) (hCbβ0 : 0 ≤ Cb / β ^ ε)
    (_hWmaster0 : 0 ≤ Wmaster)
    (_hst : 0 < s - t)
    -- THRESHOLD-SPLIT low collar term `Low = ofReal(lam₀^ε)·Wlow`:
    (Low : ℝ≥0∞) (hLowfin : Low ≠ ⊤)
    -- finiteness:
    (_hXfin : ∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε ≠ ⊤)
    (hYfin : ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε ≠ ⊤)
    (hZbfin : ∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε) ≠ ⊤)
    -- Bmaster bound: Zb.toReal ≤ Bmaster
    (hZbBm : (∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε)).toReal ≤ Bmaster)
    -- the ENNReal inequality (from the THRESHOLD-SPLIT assembly):
    (hENN : ∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
      ≤ Low + (ENNReal.ofReal (κ' * ε)
          * (∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε)
        + ENNReal.ofReal (Cb / β ^ ε) * (∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε))))
    -- C₁ chosen large: covers both the `b`-forcing AND the low collar.
    (C₁ : ℝ) (hC₁ : Cb / β ^ ε ≤ C₁) (hC₁0 : 0 ≤ C₁)
    (hLowbd : Low.toReal ≤ C₁ * Wmaster / (s - t) ^ (2 : ℝ)) :
    (∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal
      ≤ (κ * ε) * (∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal
        + C₁ * Wmaster / (s - t) ^ (2 : ℝ) + C₁ * Bmaster := by
  set X := ∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N:ℝ≥0∞)) ^ ε with hXdef
  set Y := ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N:ℝ≥0∞)) ^ ε with hYdef
  set Zb := ∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε) with hZbdef
  -- toReal-monotone applied to hENN.
  have hmono := ENNReal.toReal_mono ?_ hENN
  · -- bound RHS toReal
    rw [ENNReal.toReal_add hLowfin (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness)] at hmono
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_ofReal hCbβ0] at hmono
    -- hmono : X.toReal ≤ Low.toReal + (κ'ε * Y.toReal + (Cb/βε) * Zb.toReal)
    have hYnn : 0 ≤ Y.toReal := ENNReal.toReal_nonneg
    have hwterm : (κ' * ε) * Y.toReal ≤ (κ * ε) * Y.toReal :=
      mul_le_mul_of_nonneg_right (by nlinarith [hκ'κ, hε0]) hYnn
    have hbterm : (Cb / β ^ ε) * Zb.toReal ≤ C₁ * Bmaster :=
      mul_le_mul hC₁ hZbBm ENNReal.toReal_nonneg hC₁0
    calc X.toReal ≤ Low.toReal + ((κ' * ε) * Y.toReal + (Cb / β ^ ε) * Zb.toReal) := hmono
      _ ≤ (κ * ε) * Y.toReal + C₁ * Wmaster / (s - t) ^ (2 : ℝ) + C₁ * Bmaster := by linarith
  · -- finiteness of RHS for toReal_mono
    exact ENNReal.add_ne_top.mpr ⟨hLowfin, ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYfin,
       ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZbfin⟩⟩

-- The hole-fill lemma: assembles pillars + good-λ + toReal into the ∃ C₁ shape.
set_option maxHeartbeats 400000 in
-- Large but elementary threshold/collar bookkeeping; a modest heartbeat bump avoids spurious
-- `whnf` timeouts on the heavy `(∫⁻…).toReal` master-mass terms.
private theorem gehring_holeFill {q A ε : ℝ} (hq : 1 < q) (hA : 0 ≤ A)
    (hεpos : 0 < ε) (hεle : ε ≤ 1)
    {w b : ℂ → ℝ≥0∞} (hwmeas : AEMeasurable w volume) (hbmeas : AEMeasurable b volume)
    (x₀ : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (κ Cw Cb β : ℝ) (hCw : 0 ≤ Cw) (hCb : 0 ≤ Cb) (hβ0 : 0 < β) (hβ1 : β < 1)
    -- the κ'≤κ constant fit:
    (hκfit : Cw / ((q + ε - 1) * β ^ (q + ε - 1)) ≤ κ) (_hκ0 : 0 ≤ κ)
    -- master finiteness:
    (hWmaster0 : 0 ≤ (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal)
    (hWfin16 : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤)
    (hbfin : ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε) < ⊤)
    -- the honest, COLLAR-FREE exponent-1 good-λ (FULL `w^q` LHS, TRUNCATED super-level RHS w-mass),
    -- valid on the HIGH range `⨍_{ball s} w^q ≤ (ofReal lam)^q` (i.e. `lam ≥ lam₀`) AND above the
    -- structural collar-killing threshold `5·√Wmaster ≤ (s−t)·lam^{q/2}` (i.e. `lam ≥ lam₁`):
    (hGL : ∀ (N : ℕ) (t s : ℝ), 4 * R₀ ≤ t → t < s → s ≤ 16 * R₀ → ∀ lam : ℝ, 0 < lam →
      (⨍⁻ z in Metric.ball x₀ s, w z ^ q ∂volume) ≤ (ENNReal.ofReal lam) ^ q →
      5 * Real.sqrt ((∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal)
          ≤ (s - t) * lam ^ (q / 2) →
      ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q
        ≤ ENNReal.ofReal (Cw * lam ^ (q - 1))
            * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
          + ENNReal.ofReal Cb
            * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q)) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ N : ℕ, ∀ t s : ℝ, 4 * R₀ ≤ t → t < s → s ≤ 16 * R₀ →
      (∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal
        ≤ (κ * ε) * (∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal
          + C₁ * (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal / (s - t) ^ (2 : ℝ)
          + C₁ * (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)).toReal := by
  have hq0 : 0 < q := lt_trans one_pos hq
  have hqε0 : 0 < q + ε := by linarith
  have hqε1 : 0 < q + ε - 1 := by linarith
  set Wmaster : ℝ := (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal with hWmasterdef
  set Bmaster : ℝ := (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)).toReal with hBmasterdef
  -- The volume of `ball (4R₀)` is the smallest among `ball s` for `s ≥ 4R₀`; it gives the
  -- structural lower bound on `vol(ball s)` that bounds the threshold `lam₀^ε`.
  have hvolB4 : (0:ℝ) < Real.pi * (4 * R₀) ^ 2 := by positivity
  -- The collar constant `C₁`: covers the `b`-forcing `Cb/βε`, the low (`lam₀`) collar
  -- `lam₀^ε·Wmaster ≤ Cthr·Wmaster/(s-t)²` (using `lam₀^ε ≤ (Wmaster/vol(ball 4R₀))^{ε/q}` and
  -- `(s-t) ≤ 12R₀`), AND the collar-killing (`lam₁`) collar
  -- `lam₁^ε·(s-t)² ≤ (12R₀)² + 25·Wmaster =: Cthr1` (since `lam₁^q = 25Wmaster/(s-t)²` and
  -- `lam₁^ε ≤ 1 + lam₁^q`).  `C₁ := max (Cb/βε) (max Cthr Cthr1)`.
  set Cthr : ℝ :=
    (12 * R₀) ^ (2:ℝ) * (Wmaster / (Real.pi * (4 * R₀) ^ 2) + 1) ^ (ε / q) with hCthrdef
  have hCthr0 : 0 ≤ Cthr := by rw [hCthrdef]; positivity
  set Cthr1 : ℝ := (12 * R₀) ^ 2 + 25 * Wmaster with hCthr1def
  have hCthr10 : 0 ≤ Cthr1 := by rw [hCthr1def]; positivity
  set C₁ : ℝ := max (Cb / β ^ ε) (max Cthr Cthr1) with hC₁def
  have hC₁0 : 0 ≤ C₁ := le_trans (div_nonneg hCb (by positivity)) (le_max_left _ _)
  have hC₁ge : Cb / β ^ ε ≤ C₁ := le_max_left _ _
  have hCthrge : Cthr ≤ C₁ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCthr1ge : Cthr1 ≤ C₁ := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C₁, hC₁0, ?_⟩
  intro N t s ht hts hs
  have hst : 0 < s - t := by linarith
  have hst12 : s - t ≤ 12 * R₀ := by linarith
  -- per-N finiteness of the `Ž_N`-masses (`Ž_N(r) = ∫ w^q·(min w N)^ε ≤ N^ε·∫ w^q < ⊤`).
  have hNfin : ∀ r : ℝ, r ≤ 16 * R₀ →
      ∫⁻ z in Metric.ball x₀ r, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε ≠ ⊤ := by
    intro r hr
    have hbd : ∫⁻ z in Metric.ball x₀ r, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
        ≤ (N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q := by
      calc ∫⁻ z in Metric.ball x₀ r, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
          ≤ ∫⁻ z in Metric.ball x₀ r, w z ^ q * (N : ℝ≥0∞) ^ ε := by
            apply lintegral_mono; intro z
            exact mul_le_mul_right (ENNReal.rpow_le_rpow (min_le_right _ _) hεpos.le) _
        _ = (N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ r, w z ^ q := by
            rw [← lintegral_const_mul' _ _ (by
              exact (ENNReal.rpow_lt_top_of_nonneg hεpos.le (ENNReal.natCast_ne_top N)).ne)]
            apply lintegral_congr_ae; filter_upwards with z; rw [mul_comm]
        _ ≤ (N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q :=
            mul_le_mul_right (lintegral_mono_set (Metric.ball_subset_ball hr)) _
    refine (lt_of_le_of_lt hbd ?_).ne
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hεpos.le (ENNReal.natCast_ne_top N))
      hWfin16
  -- Bmaster bound: Zb(s).toReal ≤ Bmaster.
  have hZbBm : (∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε)).toReal ≤ Bmaster := by
    rw [hBmasterdef]
    apply ENNReal.toReal_mono hbfin.ne
    exact lintegral_mono_set (Metric.ball_subset_ball (by linarith))
  -- finiteness of ∫_{B_s} b^{q+ε}.
  have hZbsfin : ∫⁻ z in Metric.ball x₀ s, b z ^ (q + ε) ≠ ⊤ := by
    refine (lt_of_le_of_lt (lintegral_mono_set (Metric.ball_subset_ball (by linarith))) hbfin).ne
  -- ===== THRESHOLD SETUP =====
  -- The finite `w^q`-mass and average over `ball s` (a sub-ball of `16B₀`).
  have hWsfin : ∫⁻ z in Metric.ball x₀ s, w z ^ q ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono_set (Metric.ball_subset_ball (by linarith))) hWfin16).ne
  have hvolBs_pos : 0 < volume (Metric.ball x₀ s) := Metric.measure_ball_pos _ _ (by linarith)
  have hvolBs_ne : volume (Metric.ball x₀ s) ≠ 0 := hvolBs_pos.ne'
  have hvolBs_top : volume (Metric.ball x₀ s) ≠ ⊤ := measure_ball_lt_top.ne
  -- the average is finite.
  set Av : ℝ≥0∞ := ⨍⁻ z in Metric.ball x₀ s, w z ^ q ∂volume with hAvdef
  have hAvfin : Av ≠ ⊤ := by
    rw [hAvdef, setLAverage_eq]
    exact ENNReal.div_ne_top hWsfin hvolBs_ne
  -- the average threshold `lamA = Av.toReal^{1/q}` (real, ≥ 0), with `(ofReal lamA)^q = Av`.
  set lamA : ℝ := Av.toReal ^ (1 / q) with hlamAdef
  have hAvnn : 0 ≤ Av.toReal := ENNReal.toReal_nonneg
  have hlamA0 : 0 ≤ lamA := by rw [hlamAdef]; positivity
  have hlamApow : lamA ^ q = Av.toReal := by
    rw [hlamAdef, ← Real.rpow_mul hAvnn, one_div, inv_mul_cancel₀ hq0.ne', Real.rpow_one]
  have hlamAq : (ENNReal.ofReal lamA) ^ q = Av := by
    rw [ENNReal.ofReal_rpow_of_nonneg hlamA0 hq0.le, hlamApow, ENNReal.ofReal_toReal hAvfin]
  -- the collar-killing threshold `lamC = (5·√Wmaster/(s−t))^{2/q}` (real, ≥ 0), with
  -- `5·√Wmaster ≤ (s−t)·lamC^{q/2}` (with equality), so `hλ₁` holds for `lam ≥ lamC`.
  set lamC : ℝ := (5 * Real.sqrt Wmaster / (s - t)) ^ (2 / q) with hlamCdef
  have hWmsqrt0 : 0 ≤ 5 * Real.sqrt Wmaster / (s - t) := by positivity
  have hlamC0 : 0 ≤ lamC := by rw [hlamCdef]; positivity
  have hlamCq2 : lamC ^ (q / 2) = 5 * Real.sqrt Wmaster / (s - t) := by
    rw [hlamCdef, ← Real.rpow_mul hWmsqrt0]
    rw [show (2 / q) * (q / 2) = 1 by field_simp, Real.rpow_one]
  -- Make `lamC` and `lamA` opaque (their bodies are nested rpow's of heavy `.toReal`/`setLAverage`
  -- terms; downstream `nlinarith`/`positivity`/`isDefEq` only need `hlam{A,C}0`/`hlam{A,C}q2`, so
  -- keeping the bodies transparent triggers spurious `whnf` blowups).
  clear_value lamC lamA
  -- the combined assembly threshold `lam₀ = max lamA lamC ≥ 0`.
  set lam₀ : ℝ := max lamA lamC with hlam₀def
  have hlam₀0 : 0 ≤ lam₀ := le_trans hlamA0 (le_max_left _ _)
  have hlamAle : lamA ≤ lam₀ := le_max_left _ _
  have hlamCle : lamC ≤ lam₀ := le_max_right _ _
  clear_value lam₀
  -- Wlow = the master `w^q`-mass over `ball t ⊆ 16B₀`, an upper bound for every super-level mass.
  set Wlow : ℝ≥0∞ := ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q with hWlowdef
  have hWlowtop : Wlow ≠ ⊤ := hWfin16.ne
  have hWlowbound : ∀ lam : ℝ, 0 < lam →
      ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q ≤ Wlow := by
    intro lam _
    rw [hWlowdef]
    calc ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q
        ≤ ∫⁻ z in Metric.ball x₀ t, w z ^ q := lintegral_mono_set Set.inter_subset_left
      _ ≤ ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q :=
          lintegral_mono_set (Metric.ball_subset_ball (by linarith))
  -- The good-λ as consumed by the assembly: valid for `lam ≥ lam₀`.
  have hGLhigh : ∀ lam : ℝ, 0 < lam → lam₀ ≤ lam →
      ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q
        ≤ ENNReal.ofReal (Cw * lam ^ (q - 1))
            * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
          + ENNReal.ofReal Cb
            * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q) := by
    intro lam hlam hlamge
    refine hGL N t s ht hts hs lam hlam ?_ ?_
    · -- average condition: `lam ≥ lamA`.
      rw [← hAvdef, ← hlamAq]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (le_trans hlamAle hlamge)) hq0.le
    · -- collar-killing condition: `5√Wmaster ≤ (s−t)·lam^{q/2}` from `lam ≥ lamC`.
      have hlamCge : lamC ≤ lam := le_trans hlamCle hlamge
      have hpowmono : lamC ^ (q / 2) ≤ lam ^ (q / 2) :=
        Real.rpow_le_rpow hlamC0 hlamCge (by positivity)
      calc 5 * Real.sqrt Wmaster = (s - t) * lamC ^ (q / 2) := by
            rw [hlamCq2]; field_simp
        _ ≤ (s - t) * lam ^ (q / 2) := by
            apply mul_le_mul_of_nonneg_left hpowmono hst.le
  -- ENNReal inequality from the THRESHOLD-SPLIT assembly.
  have hENN := gehring_assembly hq hA hεpos hεle hwmeas hbmeas x₀ R₀ hR₀ Cw Cb β hCw hCb hβ0 hβ1
    N t s ht hts hs lam₀ hlam₀0 Wlow hWlowtop hWlowbound hGLhigh
  -- toReal conversion (κ' := Cw/((q+ε-1)β^{q+ε-1})).
  have hκ'0 : (0:ℝ) ≤ Cw / ((q + ε - 1) * β ^ (q + ε - 1)) := by
    apply div_nonneg hCw; positivity
  have hCbβ0 : (0:ℝ) ≤ Cb / β ^ ε := div_nonneg hCb (by positivity)
  -- The low collar bound: `Low = ofReal(lam₀^ε)·Wlow`, and `Low.toReal ≤ C₁·Wmaster/(s-t)²`.
  set Low : ℝ≥0∞ := ENNReal.ofReal (lam₀ ^ ε) * Wlow with hLowdef
  have hLowfin : Low ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWlowtop
  have hLowbd : Low.toReal ≤ C₁ * Wmaster / (s - t) ^ (2 : ℝ) := by
    -- `Low.toReal = lam₀^ε·Wmaster`, and `lam₀ = max lamA lamC`.
    have hWlowReal : Wlow.toReal = Wmaster := by rw [hWlowdef, hWmasterdef]
    have hLowtoReal : Low.toReal = lam₀ ^ ε * Wmaster := by
      rw [hLowdef, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hWlowReal]
    rw [hLowtoReal]
    -- helper: `(s-t)^{2:ℝ} = (s-t)^2` (natural-power), positive.
    have hst2pos : 0 < (s - t) ^ (2:ℝ) := Real.rpow_pos_of_pos hst 2
    have hst2eq : (s - t) ^ (2:ℝ) = (s - t) ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    -- SUFFICES: `lam₀^ε · (s-t)² ≤ C₁`.
    suffices hsuff : lam₀ ^ ε * (s - t) ^ (2:ℝ) ≤ C₁ by
      rw [le_div_iff₀ hst2pos]
      calc lam₀ ^ ε * Wmaster * (s - t) ^ (2:ℝ)
          = (lam₀ ^ ε * (s - t) ^ (2:ℝ)) * Wmaster := by ring
        _ ≤ C₁ * Wmaster := mul_le_mul_of_nonneg_right hsuff hWmaster0
    -- (A) the average part `lamA^ε·(s-t)² ≤ Cthr`.
    have hAvbd : Av.toReal ≤ Wmaster / (Real.pi * (4 * R₀) ^ 2) := by
      rw [hAvdef, setLAverage_eq, ENNReal.toReal_div]
      apply div_le_div₀ ENNReal.toReal_nonneg ?_ hvolB4 ?_
      · change (∫⁻ z in Metric.ball x₀ s, w z ^ q).toReal ≤ Wmaster
        rw [hWmasterdef]
        apply ENNReal.toReal_mono hWfin16.ne
        exact lintegral_mono_set (Metric.ball_subset_ball (by linarith))
      · rw [Complex.volume_ball]
        have hpi : (↑NNReal.pi : ℝ≥0∞).toReal = Real.pi := by
          rw [← NNReal.coe_real_pi]; simp
        have hs0 : (0:ℝ) ≤ s := by linarith
        rw [ENNReal.toReal_mul, ← ENNReal.ofReal_pow hs0, ENNReal.toReal_ofReal (by positivity),
          hpi]
        have h4Rs : 4 * R₀ ≤ s := by linarith only [ht, hst.le]
        have hsq : (4 * R₀) ^ 2 ≤ s ^ 2 := by
          apply pow_le_pow_left₀ (by positivity) h4Rs
        rw [mul_comm (s^2) Real.pi]
        exact mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
    have hlamAε : lamA ^ ε = Av.toReal ^ (ε / q) := by
      rw [hlamAdef, ← Real.rpow_mul hAvnn]; congr 1; ring
    have hbase_le : Av.toReal ≤ Wmaster / (Real.pi * (4 * R₀) ^ 2) + 1 :=
      le_trans hAvbd (by linarith)
    have hpow_le : Av.toReal ^ (ε / q) ≤ (Wmaster / (Real.pi * (4 * R₀) ^ 2) + 1) ^ (ε / q) :=
      Real.rpow_le_rpow hAvnn hbase_le (by positivity)
    have hAcollar : lamA ^ ε * (s - t) ^ (2:ℝ) ≤ Cthr := by
      rw [hlamAε, hCthrdef]
      calc Av.toReal ^ (ε / q) * (s - t) ^ (2:ℝ)
          ≤ (Wmaster / (Real.pi * (4 * R₀) ^ 2) + 1) ^ (ε / q) * (s - t) ^ (2:ℝ) :=
            mul_le_mul_of_nonneg_right hpow_le hst2pos.le
        _ ≤ (Wmaster / (Real.pi * (4 * R₀) ^ 2) + 1) ^ (ε / q) * (12 * R₀) ^ (2:ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_rpow hst.le hst12 (by norm_num)
        _ = (12 * R₀) ^ (2:ℝ) * (Wmaster / (Real.pi * (4 * R₀) ^ 2) + 1) ^ (ε / q) := by ring
    -- (B) the collar-killing part `lamC^ε·(s-t)² ≤ Cthr1`.
    -- `lamC^q = (5√Wm/(s-t))²` (from `lamC^{q/2} = 5√Wm/(s-t)`).
    have hlamCqval : lamC ^ q = (5 * Real.sqrt Wmaster / (s - t)) ^ 2 := by
      have h2 : lamC ^ q = (lamC ^ (q / 2)) ^ 2 := by
        rw [← Real.rpow_natCast (lamC ^ (q/2)) 2, ← Real.rpow_mul hlamC0]
        norm_num
      rw [h2, hlamCq2]
    -- `lamC^q · (s-t)² = 25·Wmaster`.
    have hlamCq_mul : lamC ^ q * (s - t) ^ 2 = 25 * Wmaster := by
      rw [hlamCqval, div_pow, div_mul_cancel₀ _ (by positivity : ((s - t) ^ 2 : ℝ) ≠ 0),
        mul_pow, Real.sq_sqrt hWmaster0]; ring
    -- `lamC^ε ≤ 1 + lamC^q` (since `0 ≤ ε ≤ q`).
    have hlamCε_le : lamC ^ ε ≤ 1 + lamC ^ q := by
      rcases le_or_gt lamC 1 with hle | hgt
      · have hle1 : lamC ^ ε ≤ 1 := Real.rpow_le_one hlamC0 hle hεpos.le
        linarith only [Real.rpow_nonneg hlamC0 q, hle1]
      · have hle2 : lamC ^ ε ≤ lamC ^ q :=
          Real.rpow_le_rpow_of_exponent_le hgt.le (le_trans hεle (le_of_lt hq))
        linarith only [hle2]
    have hst2le : (s - t) ^ 2 ≤ (12 * R₀) ^ 2 := by
      apply pow_le_pow_left₀ hst.le hst12
    have hCcollar : lamC ^ ε * (s - t) ^ (2:ℝ) ≤ Cthr1 := by
      calc lamC ^ ε * (s - t) ^ (2:ℝ)
          ≤ (1 + lamC ^ q) * (s - t) ^ (2:ℝ) :=
            mul_le_mul_of_nonneg_right hlamCε_le hst2pos.le
        _ = (s - t) ^ 2 + lamC ^ q * (s - t) ^ 2 := by rw [hst2eq]; ring
        _ = (s - t) ^ 2 + 25 * Wmaster := by rw [hlamCq_mul]
        _ ≤ (12 * R₀) ^ 2 + 25 * Wmaster := by linarith only [hst2le]
        _ = Cthr1 := hCthr1def.symm
    -- Combine: `lam₀^ε = max(lamA^ε, lamC^ε)`, bounded by `max(Cthr,Cthr1) ≤ C₁`.
    have hmaxpow : lam₀ ^ ε = max (lamA ^ ε) (lamC ^ ε) := by
      rw [hlam₀def]
      rcases le_total lamA lamC with h | h
      · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow hlamA0 h hεpos.le)]
      · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow hlamC0 h hεpos.le)]
    rw [hmaxpow]
    rcases le_total (lamA ^ ε) (lamC ^ ε) with h | h
    · rw [max_eq_right h]; exact le_trans hCcollar hCthr1ge
    · rw [max_eq_left h]; exact le_trans hAcollar hCthrge
  exact gehring_toReal_conv (κ' := Cw / ((q + ε - 1) * β ^ (q + ε - 1)))
    (Wmaster := Wmaster) (Bmaster := Bmaster) N hκfit hκ'0
    hεpos.le hCbβ0 hWmaster0 hst Low hLowfin (hNfin t (by linarith)) (hNfin s hs) hZbsfin hZbBm hENN
    C₁ hC₁ge hC₁0 hLowbd


/-- **S2 (`gehring_selfImprovement`).** The **abstract Gehring reverse-Hölder
self-improvement lemma**, stated equation-agnostically so it is reusable.

Fix an exponent `q > 1` and a reverse-Hölder constant `A ≥ 0`. Then there is a *single*
exponent gain `ε > 0` — depending only on `q` and `A` (and the ambient dimension `2`) —
such that **every** nonnegative weight `w : ℂ → ℝ≥0∞` that is locally `Lᵠ` (together with a
lower-order term `b` locally `Lᵠ`) and satisfies the **reverse-Hölder inequality** on every
ball `B = ball x r` with the **fixed enlargement factor `4`** (`4B = ball x (4r)`),
`(⨍⁻_{B} wᵠ)^(1/q) ≤ A · ⨍⁻_{4B} w + (⨍⁻_{4B} bᵠ)^(1/q)`,
is self-improved to `w ∈ L^{q+ε}_loc`, quantitatively on every compact `K`:
`∫⁻_{K} w^{q+ε} < ⊤`. (Gehring's lemma is robust to any fixed enlargement `> 1`; the factor
`4` is the one produced by the asymmetric Sobolev–Poincaré chain in S1.)

**Uniformity of `ε`.** The gain is quantified *outside* the weight `w` (and `b`): it
depends only on the structural constants `q, A`. This is the precise classical statement
of Gehring's lemma, and is exactly what the Beltrami consumer needs (the cutoff fixed
points share one `A`, hence one `ε`).

This is the content underlying Gehring's lemma; the proof runs the good-λ /
stopping-time / Calderón–Zygmund decomposition through the Hardy–Littlewood maximal
function (`maximalFunction` and its weak-(1,1)/strong-(p,p) bounds), a Vitali
covering (`Vitali.exists_disjoint_subfamily_covering_enlargement_ball`), and the
layer-cake formula (`lintegral_eq_lintegral_meas_lt`). -/
theorem gehring_selfImprovement {q A : ℝ} (hq : 1 < q) (hA : 0 ≤ A) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
      ∀ {w b : ℂ → ℝ≥0∞}, AEMeasurable w volume → AEMeasurable b volume →
        (∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, w z ^ q < ⊤) →
        (∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, b z ^ (q + ε) < ⊤) →
        (∀ (x : ℂ) (r : ℝ), 0 < r →
          (⨍⁻ z in Metric.ball x r, w z ^ q ∂volume) ^ (1 / q) ≤
            ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), w z ∂volume) +
              ENNReal.ofReal A * (⨍⁻ z in Metric.ball x (4 * r), b z ^ q ∂volume) ^ (1 / q)) →
        ∀ K : Set ℂ, IsCompact K → ∫⁻ z in K, w z ^ (q + ε) < ⊤ := by
  -- ===========================================================================
  -- DECOMPOSITION of the abstract Gehring self-improvement lemma into the four
  -- dependency-ordered nodes G0 (localization), G1 (good-λ / Calderón–Zygmund),
  -- G2 (layer-cake + ε-absorption) and G3 (glue), following the standard proof.
  --
  -- The structure is exactly the classical one: G1 is the genuine good-λ
  -- inequality produced by the maximal-function stopping decomposition + the
  -- Vitali covering + the per-ball reverse-Hölder hypothesis; G2 integrates G1
  -- against `λ^{ε-1}` via the layer-cake formula and absorbs the resulting
  -- `∫ w^{q+ε}` term on the left using `ε` small. G0 reduces the compact-set
  -- conclusion to a fixed enclosing ball, and G3 is the trivial glue. The output
  -- exponent gain `ε₀` is the one extracted by the absorption in G2: it is read off
  -- from the absorbed coefficient (the rate `κ`, fixed by `q, A`) as `ε₀ = 1/(2κ+1)`.
  -- ===========================================================================
  classical
  -- =========================================================================
  -- HONEST GAIN `ε₀`.  The absorption in G2 produces an absorbed coefficient
  -- `θ(ε) = κ·ε` (the hole-filling `θ` fed to `giaquinta_iteration`), where the
  -- absorption RATE `κ` depends ONLY on the structural data `q, A` (it is read off
  -- the good-λ covering constant, which is `w,b`-independent), NOT on `ε`.  So we
  -- can extract `κ` here — before `ε`, `w`, `b` enter — and set
  --   `ε₀ := 1 / (2κ + 1)`,
  -- which forces `θ = κ·ε ≤ κ·ε₀ = κ/(2κ+1) < 1/2 < 1` for every `ε ≤ ε₀`, so the
  -- Giaquinta absorption succeeds.  (The gain must scale with `1/κ`: for `ε` large the
  -- absorbed coefficient would exceed `1` and the absorption would fail.)  `κ` is a
  -- concrete closed form in `q, A`: with the
  -- collar-free good-λ constants `Cw = 256·Ã·lam^{q-1}`, `β = 1/(4Ã)` (`Ã = π^{1/q}A+1`),
  -- the absorbed rate `Cw/((q+ε−1)·β^{q+ε−1}) = 256·Ã·(4Ã)^{q+ε−1}/(q+ε−1)` is `≤`
  -- the ε-uniform `C₀/(q−1)` with `C₀ := 256·Ã·(4Ã)^q` (since `4Ã ≥ 4 > 1` makes
  -- `(4Ã)^{ε−1} ≤ 1` and `1/(q+ε−1) ≤ 1/(q−1)` for `ε ≤ 1`).
  -- =========================================================================
  have hq0' : 0 < q := lt_trans one_pos hq
  have hq1 : 0 < q - 1 := by linarith
  set Ãκ : ℝ := Real.pi ^ (1 / q) * A + 1 with hÃκdef
  have hÃκpos : 0 < Ãκ := by rw [hÃκdef]; positivity
  set C₀ : ℝ := 256 * Ãκ * (4 * Ãκ) ^ q with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; positivity
  set κ : ℝ := C₀ / (q - 1) with hκdef
  have hκpos : 0 < κ := by rw [hκdef]; exact div_pos hC₀pos hq1
  have hκ0 : 0 ≤ κ := hκpos.le
  set ε₀ : ℝ := 1 / (2 * κ + 1) with hε₀def
  have hε₀pos : 0 < ε₀ := by rw [hε₀def]; positivity
  -- For every `ε ≤ ε₀`, the absorbed coefficient `θ = κ·ε` is `< 1`.
  have hθlt1 : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → κ * ε < 1 := by
    intro ε hεpos hεle
    have h1 : κ * ε ≤ κ * ε₀ := mul_le_mul_of_nonneg_left hεle hκ0
    have h2 : κ * ε₀ = κ / (2 * κ + 1) := by rw [hε₀def]; ring
    have h3 : κ / (2 * κ + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro ε hεpos hεle w b hwmeas hbmeas hwloc hbloc hRH
  -- The honest absorbed coefficient for this `ε`.
  have hθε : κ * ε < 1 := hθlt1 ε hεpos hεle
  have hκε0 : 0 ≤ κ * ε := by positivity
  -- ---------------------------------------------------------------------------
  -- G0 + G3 (localization + glue) — CLOSED.
  -- It suffices to prove the fixed-ball finiteness `∫⁻_{ball x₀ R₀} w^{q+ε} < ⊤`
  -- for every centre `x₀` and radius `R₀ > 0`: a compact `K` is bounded, hence
  -- contained in some ball `ball 0 R₀`, and `∫⁻_K ≤ ∫⁻_{ball 0 R₀}` by monotonicity.
  -- ---------------------------------------------------------------------------
  suffices hball : ∀ (x₀ : ℂ) (R₀ : ℝ), 0 < R₀ →
      ∫⁻ z in Metric.ball x₀ R₀, w z ^ (q + ε) < ⊤ by
    intro K hK
    obtain ⟨R₀, hR₀sub⟩ := hK.isBounded.subset_ball 0
    rcases le_or_gt R₀ 0 with hR₀ | hR₀
    · -- `R₀ ≤ 0` ⟹ `ball 0 R₀ = ∅` ⟹ `K = ∅`.
      have hKsub : K ⊆ (∅ : Set ℂ) := by
        intro z hz
        have := hR₀sub hz
        rwa [Metric.ball_eq_empty.mpr hR₀] at this
      rw [Set.subset_empty_iff.mp hKsub]; simp
    · calc ∫⁻ z in K, w z ^ (q + ε)
          ≤ ∫⁻ z in Metric.ball 0 R₀, w z ^ (q + ε) := lintegral_mono_set hR₀sub
        _ < ⊤ := hball 0 R₀ hR₀
  -- ---------------------------------------------------------------------------
  -- Fix the enclosing ball `B₀ = ball x₀ R₀` (`R₀ > 0`).
  -- ---------------------------------------------------------------------------
  intro x₀ R₀ hR₀
  -- Basic positivity facts about `q` and `ε` reused below.
  have hq0 : 0 < q := lt_trans one_pos hq
  have hqε0 : 0 < q + ε := by linarith
  -- ===========================================================================
  -- G1 (good-λ / Calderón–Zygmund) — the FIRST hard node.
  --
  -- The Giaquinta–Modica good-λ inequality at the heart of Gehring's lemma.  For
  -- a level `λ ≥ λ₀` the super-level `wᵠ`-mass over the master ball `4B₀` is
  -- controlled by a `λ^{q-1}`-weighted mass of `w` at EXPONENT ONE over a smaller
  -- super-level set, plus a super-level `bᵠ`-forcing:
  --   `∫_{{w>λ}∩4B₀} wᵠ  ≤  C · λ^{q-1} · ∫_{{w>βλ}∩16B₀} w
  --                           + C · ∫_{{b>βλ}∩16B₀} bᵠ`,
  -- with `0 < β < 1` and a FIXED constant `C` (depending only on `q`, `A` and the
  -- planar doubling/overlap constant).  Three features are load-bearing:
  --  * the exponent `1` on the right `w`-mass together with the `λ^{q-1}` factor
  --    make the G2 layer-cake absorbed coefficient `K(ε) = C·ε/((q+ε−1)·β^{q+ε−1})`
  --    tend to `0` as `ε → 0` (the ε-prefactor survives because the radial inner
  --    integral over `λ^{q+ε−2}` stays bounded, `q+ε−2 > −1`), so a FIXED `C` is
  --    absorbed for small `ε` — the constant need NOT shrink;
  --  * the forcing is a SUPER-LEVEL set of `b` at exponent `q`, not a λ-independent
  --    constant (which would make `∫_{λ₀}^∞ λ^{ε−1} dλ` diverge);
  --  * the threshold `λ₀ ~ (⨍_{4B₀} wᵠ)^{1/q}` is genuine: for `λ < λ₀` the
  --    inequality fails (as `λ → 0` the left side → `∫_{4B₀} wᵠ > 0` while the
  --    `λ^{q-1}`-weighted right `w`-term → `0`).
  --
  -- Mathematically this is the Calderón–Zygmund stopping decomposition of `wᵠ` at
  -- height `λ^q` on `4B₀` (`Vitali.exists_disjoint_subfamily_covering_enlargement_ball`,
  -- `Set.Countable.measure_biUnion_le_lintegral`): each stopping ball `Bᵢ ⊆ 4B₀`
  -- has `⨍_{Bᵢ} wᵠ > λ^q`, and the per-ball reverse-Hölder inequality `hRH` on the
  -- enlargement `4Bᵢ ⊆ 16B₀` splits `Bᵢ` into `w`-dominated balls (`⨍_{4Bᵢ} w > cλ`,
  -- contributing the `λ^{q-1}·∫_{{w>βλ}} w` term) and `b`-dominated balls
  -- (`⨍_{4Bᵢ} bᵠ > c'λ^q`, contributing `∫_{{b>βλ}} bᵠ`).
  -- ===========================================================================
  -- The two finite forcing masses over the master super-ball `16B₀`, available from
  -- the loc-`Lᵠ` / loc-`L^{q+ε}` hypotheses; we expose their `.toReal` (real, finite)
  -- as the data `A`-/`B`-constants of the hole-filling inequality.
  have hWmaster : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set Metric.ball_subset_closedBall)
      (hwloc _ (isCompact_closedBall x₀ (16 * R₀)))
  have hBmaster : ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set Metric.ball_subset_closedBall)
      (hbloc _ (isCompact_closedBall x₀ (16 * R₀)))
  set Wmaster : ℝ := (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal with hWmasterdef
  set Bmaster : ℝ := (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)).toReal with hBmasterdef
  have hWmaster0 : 0 ≤ Wmaster := ENNReal.toReal_nonneg
  have hBmaster0 : 0 ≤ Bmaster := ENNReal.toReal_nonneg
  -- =========================================================================
  -- G1 (good-λ / Calderón–Zygmund), in its HOLE-FILLING form.  The classical
  -- good-λ inequality, run over a chain of concentric
  -- radii `4R₀ ≤ t < s ≤ 16R₀` (the good-λ holds for every such pair because
  -- every ball satisfies `hRH`) and integrated against `λ^{ε-1}` via the
  -- layer-cake / Cavalieri formula, produces directly the hole-filling
  -- inequality that the Giaquinta–Giusti iteration lemma `giaquinta_iteration`
  -- consumes:  with the absorbed coefficient `θ = κ·ε < 1` (κ fixed by
  -- `q, A`), for every truncation level `N` and every `4R₀ ≤ t < s ≤ 16R₀`,
  --   `Z_N(t) ≤ (κ·ε)·Z_N(s) + C₁·Wmaster/(s−t)² + C₁·Bmaster`,
  -- where `Z_N(t) := (∫_{ball x₀ t}(min w N)^{q+ε}).toReal` is the truncated
  -- `(q+ε)`-mass, `C₁ ≥ 0` is a FIXED constant (independent of `N`, `t`, `s`),
  -- and `Wmaster, Bmaster` are the finite master forcing masses.  The exponent-1
  -- structure of the right `w`-mass is what makes `θ = κ·ε`, hence `< 1` for
  -- `ε ≤ ε₀`.
  --
  -- The Calderón–Zygmund COVERING CORE is `gehring_goodLambda_measure` (good-λ super-level
  -- measure bound via the Vitali/Carleson engine + Lebesgue differentiation
  -- `gehring_density_ball` + the planar doubling engine `gehring_engine_bound`):
  --   `vol {z∈ball x₀ t | lam < (min w N) z}
  --       ≤ ofReal((2(A+1)/lam)·16)·∫_{ball x₀ s} w
  --         + ofReal((2(A+1)/lam)^q·16)·∫_{ball x₀ s} bᵠ`.
  -- The layer-cake λ-integration of that
  -- bound (`holeFill_layerCake`) plus the ε-absorption upgrades the
  -- good-λ RHS from the FULL `∫_{ball s} w` to the SUPER-LEVEL-restricted
  -- `∫_{{w>βλ}∩ball s} (min w N)` so that the Tonelli reconstruction returns
  -- `Z_N(s)` (not the unbounded `∫_s w^p`); that upgrade uses the TWO-SIDED dyadic
  -- stopping `exists_dyadic_CZ_stopping` (`lam < ⨍_Q wᵠ ≤ 4 lam`, in
  -- `DyadicLebesgue`) to force `w ≈ min w N` on the selected cubes.
  -- The full-RHS good-λ alone is insufficient (its
  -- λ-integral over `(0,∞)` diverges, and the cap at `N` is not `N`-uniform).
  -- =========================================================================
  obtain ⟨C₁, hC₁0, holeFill⟩ :
      ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ N : ℕ, ∀ t s : ℝ, 4 * R₀ ≤ t → t < s → s ≤ 16 * R₀ →
        (∫⁻ z in Metric.ball x₀ t, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal
          ≤ (κ * ε) * (∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal
            + C₁ * Wmaster / (s - t) ^ (2 : ℝ) + C₁ * Bmaster := by
    -- ε ≤ 1 (since ε ≤ ε₀ = 1/(2κ+1) ≤ 1).
    have hεle1 : ε ≤ 1 := le_trans hεle (by rw [hε₀def, div_le_one (by positivity)]; linarith)
    -- The honest COLLAR-FREE good-λ constants (depend only on q, A); `Ã = π^{1/q}A+1`,
    -- `Cw = 256Ã`, `Cb = 64(4Ã)^q`, `β = 1/(4Ã)` (exactly `gehring_goodLambda_integral_noCollar`).
    set P : ℝ := Real.pi ^ (1 / q) with hPdef
    have hPpos : 0 < P := by rw [hPdef]; positivity
    set Ã : ℝ := P * A + 1 with hÃdef
    have hÃpos : 0 < Ã := by rw [hÃdef]; positivity
    set Cw : ℝ := 256 * Ã with hCwdef
    set Cb : ℝ := 64 * (4 * Ã) ^ q with hCbdef
    set β : ℝ := 1 / (4 * Ã) with hβdef
    have hCwpos : 0 ≤ Cw := by rw [hCwdef]; positivity
    have hCbpos : 0 ≤ Cb := by rw [hCbdef]; positivity
    have hβpos : 0 < β := by rw [hβdef]; positivity
    have h4Ãgt1 : (1:ℝ) < 4 * Ã := by rw [hÃdef]; nlinarith [hPpos, hA]
    have h4Ãge1 : (1:ℝ) ≤ 4 * Ã := h4Ãgt1.le
    have hβ1 : β < 1 := by
      rw [hβdef, div_lt_one (by positivity)]; linarith [h4Ãgt1]
    -- The constant fit `κ' ≤ κ`.  `Cw/((q+ε−1)·β^{q+ε−1}) = 256Ã·(4Ã)^{q+ε−1}/(q+ε−1)`,
    -- and `(4Ã)^{ε−1} ≤ 1` (base `≥ 1`, exponent `≤ 0`), `1/(q+ε−1) ≤ 1/(q−1)`, so this is
    -- `≤ 256Ã·(4Ã)^q/(q−1) = C₀/(q−1) = κ`.
    have hκfit : Cw / ((q + ε - 1) * β ^ (q + ε - 1)) ≤ κ := by
      have hq1' : 0 < q - 1 := by linarith
      have hqε1' : 0 < q + ε - 1 := by linarith
      have hÃ4pos : (0:ℝ) < 4 * Ã := by positivity
      -- `β^{q+ε-1} = (4Ã)^{-(q+ε-1)}`, so `1/β^{q+ε-1} = (4Ã)^{q+ε-1}`.
      have hβpow : β ^ (q + ε - 1) = (4 * Ã) ^ (-(q + ε - 1)) := by
        rw [hβdef, Real.div_rpow (by norm_num) (by positivity), Real.one_rpow,
          Real.rpow_neg (by positivity), one_div]
      have hden_pos : 0 < (q + ε - 1) * β ^ (q + ε - 1) := by
        rw [hβpow]; positivity
      rw [hκdef, hC₀def, hCwdef, div_le_div_iff₀ hden_pos hq1', hβpow]
      -- LHS = 256Ã·(q-1), RHS = 256Ã(4Ã)^q·((q+ε-1)·(4Ã)^{-(q+ε-1)}).
      rw [Real.rpow_neg (by positivity)]
      have h4Ãqpos : (0:ℝ) < (4 * Ã) ^ q := Real.rpow_pos_of_pos hÃ4pos q
      have h4Ãqεpos : (0:ℝ) < (4 * Ã) ^ (q + ε - 1) := Real.rpow_pos_of_pos hÃ4pos _
      -- `(4Ã)^{ε-1} ≤ 1` (base ≥ 1, exponent ≤ 0), hence `(4Ã)^{q+ε-1} ≤ (4Ã)^q`.
      have hle1 : (4 * Ã) ^ (ε - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos h4Ãge1 (by linarith [hεle1])
      have hqεle : (4 * Ã) ^ (q + ε - 1) ≤ (4 * Ã) ^ q := by
        rw [show q + ε - 1 = q + (ε - 1) by ring, Real.rpow_add hÃ4pos]
        calc (4 * Ã) ^ q * (4 * Ã) ^ (ε - 1) ≤ (4 * Ã) ^ q * 1 :=
              mul_le_mul_of_nonneg_left hle1 h4Ãqpos.le
          _ = (4 * Ã) ^ q := mul_one _
      -- RHS = 256Ã(4Ã)^q·(q+ε-1)/(4Ã)^{q+ε-1} ≥ 256Ã·(q+ε-1) ≥ 256Ã·(q-1).
      rw [show 256 * Ã * (4 * Ã) ^ q * ((q + ε - 1) * ((4 * Ã) ^ (q + ε - 1))⁻¹)
            = (256 * Ã * (q + ε - 1)) * ((4 * Ã) ^ q / (4 * Ã) ^ (q + ε - 1)) by
          rw [div_eq_mul_inv]; ring]
      have hfrac_ge1 : (1:ℝ) ≤ (4 * Ã) ^ q / (4 * Ã) ^ (q + ε - 1) :=
        (one_le_div₀ h4Ãqεpos).mpr hqεle
      have hstep : 256 * Ã * (q - 1) ≤ 256 * Ã * (q + ε - 1) := by nlinarith [hÃpos, hεpos]
      calc 256 * Ã * (q - 1) ≤ 256 * Ã * (q + ε - 1) := hstep
        _ = (256 * Ã * (q + ε - 1)) * 1 := by ring
        _ ≤ (256 * Ã * (q + ε - 1)) * ((4 * Ã) ^ q / (4 * Ã) ^ (q + ε - 1)) :=
            mul_le_mul_of_nonneg_left hfrac_ge1 (by positivity)
    -- The honest exponent-1 good-λ (STEP B).  It is assembled from the
    -- `Ž_N = ∫ w^q·(min w N)^ε`-layer-cake `gehring_mass_layerCake`, its
    -- reconstruction `gehring_recon` + the tail-killing pointwise comparison `gehring_crux_le`, the
    -- ε-absorption assembly `gehring_assembly`, the `.toReal` conversion `gehring_toReal_conv`, the
    -- hole-fill packaging `gehring_holeFill`, and the constant fit `hκfit`.  This `hGL` is the
    -- good-λ: the FULL (a-priori-integrable) `w^q`
    -- mass on the super-level set `{min w N > lam} ∩ ball t` is controlled by the
    -- `lam^{q-1}`-weighted
    -- FULL `w`-mass (exponent one) on the SUPER-LEVEL set `{min w N > β·lam} ∩ ball s`, plus a
    -- super-level `bᵠ`-forcing.  Crucially the RHS w-mass is the FULL `w` (no `min w N` truncation
    -- of the integrand) — this is exactly what the dyadic-CZ stopping + reverse-Hölder dichotomy +
    -- Carleson engine produce (no enlarged-ball maximal upper bound on `⨍ w` is required).
    -- The truncation `min w N` lives ONLY in the level set (truncated super-level), which on the
    -- active range `lam < N` agrees with `{w > β·lam}`; for `lam ≥ N` the LHS super-level set is
    -- empty so the inequality is trivial.  The over-truncation tail is handled
    -- by `gehring_crux_le` (the iterated quantity is `Ž_N = ∫ w^q·(min w N)^ε`, FINITE,
    -- with the truncation on the `ε`-factor only), NOT by truncating the good-λ RHS integrand.
    have hGL : ∀ (N : ℕ) (t s : ℝ), 4 * R₀ ≤ t → t < s → s ≤ 16 * R₀ → ∀ lam : ℝ, 0 < lam →
        (⨍⁻ z in Metric.ball x₀ s, w z ^ q ∂volume) ≤ (ENNReal.ofReal lam) ^ q →
        5 * Real.sqrt ((∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal)
            ≤ (s - t) * lam ^ (q / 2) →
        ∫⁻ z in Metric.ball x₀ t ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z ^ q
          ≤ ENNReal.ofReal (Cw * lam ^ (q - 1))
              * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (min (w z) (N:ℝ≥0∞)).toReal}, w z)
            + ENNReal.ofReal Cb
              * (∫⁻ z in Metric.ball x₀ s ∩ {z | β * lam < (b z).toReal}, b z ^ q) := by
      intro N t' s' ht' hts' hs' lam hlampos hlam0cond hlam1cond
      -- The `min w N` level sets reduce to the FULL `w` level sets up to the null set `{w = ⊤}`
      -- exactly when `lam < N` (and `β·lam < lam < N`); the integral good-λ pillar then closes it.
      -- For `lam ≥ N` the LHS super-level set `{lam < (min w N).toReal}` is empty.
      have hWfin16 : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤ := hWmaster
      classical
      -- `{w = ⊤} ∩ ball x₀ (16R₀)` is `volume`-null (`w^q` integrable there ⟹ `w < ⊤` a.e.).
      have hwtop_null : volume ({z : ℂ | w z = ⊤} ∩ Metric.ball x₀ (16 * R₀)) = 0 := by
        have htop :
            volume {z : ℂ | (Metric.ball x₀ (16 * R₀)).indicator (fun z => w z ^ q) z = ⊤} = 0 := by
          apply measure_eq_top_of_lintegral_ne_top
            ((hwmeas.pow_const q).indicator measurableSet_ball)
          rw [lintegral_indicator measurableSet_ball]; exact hWfin16.ne
        refine measure_mono_null ?_ htop
        intro z hz; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hz ⊢
        rw [Set.indicator_of_mem hz.2, hz.1, ENNReal.top_rpow_of_pos (by linarith : (0:ℝ) < q)]
      -- The level-set equality up to `{w = ⊤}` (null on the ball), via symmetric-difference
      -- nullity.
      have hset_eq : ∀ (r c : ℝ), r ≤ 16 * R₀ → c < (N:ℝ) →
          (Metric.ball x₀ r ∩ {z : ℂ | c < (min (w z) (N:ℝ≥0∞)).toReal} : Set ℂ)
            =ᵐ[volume] (Metric.ball x₀ r ∩ {z : ℂ | c < (w z).toReal} : Set ℂ) := by
        intro r c hr hcN
        have hnull : volume ({z : ℂ | w z = ⊤} ∩ Metric.ball x₀ r) = 0 :=
          measure_mono_null (Set.inter_subset_inter_right _ (Metric.ball_subset_ball hr)) hwtop_null
        rw [Filter.eventuallyEq_set, ae_iff]
        refine measure_mono_null
          (show {z : ℂ | ¬ (z ∈ Metric.ball x₀ r ∩ {z | c < (min (w z) (N:ℝ≥0∞)).toReal}
              ↔ z ∈ Metric.ball x₀ r ∩ {z | c < (w z).toReal})}
            ⊆ {z : ℂ | w z = ⊤} ∩ Metric.ball x₀ r from ?_) hnull
        intro z hz
        simp only [Set.mem_ofPred_eq] at hz
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        by_cases hzr : z ∈ Metric.ball x₀ r
        · refine ⟨?_, hzr⟩
          by_contra hwtop
          apply hz
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hzr, true_and]
          rw [ENNReal.toReal_min hwtop (ENNReal.natCast_ne_top N), ENNReal.toReal_natCast]
          constructor
          · intro h2; exact lt_of_lt_of_le h2 (min_le_left _ _)
          · intro h2; exact lt_min h2 hcN
        · exact absurd (by simp only [Set.mem_inter_iff, hzr, false_and, iff_self]) hz
      -- `∫_{16B₀} b^q < ⊤` from the loc-`L^{q+ε}` master mass `hBmaster` (`b^q ≤ 1 + b^{q+ε}`).
      have hBfinq : ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ q < ⊤ := by
        have hbd : ∀ z, b z ^ q ≤ 1 + b z ^ (q + ε) := by
          intro z
          rcases le_total (b z) 1 with hle | hge
          · have : b z ^ q ≤ 1 := by
              rw [← ENNReal.one_rpow q]; exact ENNReal.rpow_le_rpow hle hq0.le
            exact le_trans this (le_add_right le_rfl)
          · have : b z ^ q ≤ b z ^ (q + ε) :=
              ENNReal.rpow_le_rpow_of_exponent_le hge (by linarith)
            exact le_trans this (le_add_left le_rfl)
        calc ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ q
            ≤ ∫⁻ z in Metric.ball x₀ (16 * R₀), (1 + b z ^ (q + ε)) := lintegral_mono hbd
          _ = volume (Metric.ball x₀ (16 * R₀))
                + ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε) := by
              rw [lintegral_add_left' aemeasurable_const, setLIntegral_const, one_mul]
          _ < ⊤ := ENNReal.add_lt_top.mpr ⟨measure_ball_lt_top, hBmaster⟩
      rcases lt_or_ge lam (N : ℝ) with hlamN | hlamN
      · -- `lam < N`: a.e. rewrite both `min w N` level sets to full `w` level sets.
        have hβlamN : β * lam < (N:ℝ) := by
          have : β * lam < lam := by
            rw [hβdef]
            calc 1 / (4 * Ã) * lam < 1 * lam := by
                  apply mul_lt_mul_of_pos_right _ hlampos
                  rw [div_lt_one (by positivity)]; linarith [h4Ãge1]
              _ = lam := one_mul lam
          linarith
        rw [setLIntegral_congr (hset_eq t' lam (by linarith) hlamN),
            setLIntegral_congr (hset_eq s' (β * lam) hs' hβlamN)]
        have hcall := gehring_goodLambda_integral_noCollar hq hA hwmeas hbmeas hRH x₀ R₀ hR₀
          hWfin16 hBfinq t' s' ht' hts' hs' lam hlampos hlam0cond hlam1cond
        -- The noCollar bound's constants/level match `Cw, Cb, β` (via `hÃdef`, `hβdef`, `hCwdef`,
        -- `hCbdef`); rewrite to identify them.
        rw [show (256 : ℝ) * (Real.pi ^ (1 / q) * A + 1) * lam ^ (q - 1) = Cw * lam ^ (q - 1) by
              rw [hCwdef, hÃdef, hPdef],
            show (64 : ℝ) * (4 * (Real.pi ^ (1 / q) * A + 1)) ^ q = Cb by rw [hCbdef, hÃdef, hPdef],
            show (1 : ℝ) / (4 * (Real.pi ^ (1 / q) * A + 1)) = β by
              rw [hβdef, hÃdef, hPdef]] at hcall
        exact hcall
      · -- `lam ≥ N`: the LHS super-level set is empty, so the LHS is `0`.
        have hempty :
            Metric.ball x₀ t' ∩ {z | lam < (min (w z) (N:ℝ≥0∞)).toReal} = (∅ : Set ℂ) := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro z ⟨_, hlt⟩
          simp only [Set.mem_ofPred_eq] at hlt
          have hle : (min (w z) (N:ℝ≥0∞)).toReal ≤ (N:ℝ) := by
            rcases eq_or_ne (w z) ⊤ with hwt | hwf
            · rw [hwt]; simp
            · rw [ENNReal.toReal_min hwf (ENNReal.natCast_ne_top N), ENNReal.toReal_natCast]
              exact min_le_right _ _
          linarith
        rw [hempty]; simp
    exact gehring_holeFill hq hA hεpos hεle1 hwmeas hbmeas x₀ R₀ hR₀ κ Cw Cb β
      hCwpos hCbpos hβpos hβ1 hκfit hκ0 hWmaster0 hWmaster hBmaster hGL
  -- ===========================================================================
  -- G2 (layer-cake + ε-absorption) — the SECOND hard node.
  --
  -- Multiply the MASTER-BALL good-λ inequality `goodLambda` by `λ^{ε-1}` and
  -- integrate in `λ ∈ (0,∞)`. By the layer-cake / Cavalieri representation
  -- (`lintegral_rpow_eq_lintegral_meas_lt_mul`) the left side reconstructs
  -- `∫_{4B₀} w^{q+ε}`, and — now that the good-λ RHS `wᵠ`-mass lives over the SAME
  -- master ball `4B₀` — the first right-hand term reconstructs into a term over
  -- `∫_{4B₀} w^{q+ε}` as well (Giaquinta–Modica iteration lemma); the absorbed
  -- coefficient is `< 1` for `ε ≤ ε₀` small, so the `∫_{4B₀} w^{q+ε}` term moves
  -- to the left, leaving
  --   `∫_{4B₀} w^{q+ε} ≲ ∫_{16B₀} wᵠ + ∫_{16B₀} b^{q+ε} < ⊤`,
  -- finite by the loc-`Lᵠ` hypothesis `hwloc` on `wᵠ` and the loc-`L^{q+ε}`
  -- hypothesis `hbloc` on `b`, both evaluated on the compact `closedBall x₀ (16 R₀)`.
  --
  -- The absorption is the only place the smallness of `ε` is used; it is what
  -- fixes the gain `ε₀`. This node consumes the master-ball `goodLambda`; the
  -- layer-cake bookkeeping and the absorption inequality live here.
  -- ===========================================================================
  have absorb : ∫⁻ z in Metric.ball x₀ R₀, w z ^ (q + ε) < ⊤ := by
    -- The forcing terms G2 produces on the right are finite, from the
    -- loc-`Lᵠ`/loc-`L^{q+ε}` hypotheses, evaluated on the
    -- compact super-ball `closedBall x₀ (16 R₀)` (which contains `16B₀`).
    -- `∫_{16B₀} wᵠ < ⊤` from `hwloc`.
    have hRHS_w : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤ := by
      have hKc : IsCompact (Metric.closedBall x₀ (16 * R₀)) :=
        isCompact_closedBall x₀ (16 * R₀)
      exact lt_of_le_of_lt (lintegral_mono_set Metric.ball_subset_closedBall) (hwloc _ hKc)
    -- `∫_{16B₀} b^{q+ε} < ⊤` from `hbloc`.
    have hRHS_b : ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε) < ⊤ := by
      have hKc : IsCompact (Metric.closedBall x₀ (16 * R₀)) :=
        isCompact_closedBall x₀ (16 * R₀)
      exact lt_of_le_of_lt (lintegral_mono_set Metric.ball_subset_closedBall) (hbloc _ hKc)
    -- `B₀ ⊆ 4B₀`, so it suffices to bound `∫_{4B₀} w^{q+ε}`.
    have hsub : Metric.ball x₀ R₀ ⊆ Metric.ball x₀ (4 * R₀) :=
      Metric.ball_subset_ball (by linarith)
    refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
    -- =======================================================================
    -- CORE of G2: the layer-cake reconstruction + ε-absorption.
    --
    -- The node is a SINGLE absorbed linear bound of the target
    -- `∫_{4B₀} w^{q+ε}` by the two finite forcing masses `∫_{16B₀} wᵠ` and
    -- `∫_{16B₀} b^{q+ε}` (both `< ⊤`, supplied above as `hRHS_w`, `hRHS_b`) with
    -- a FINITE coefficient `K`, packaged as `hbound`; the finiteness wrapper around
    -- it (below) follows from `hRHS_w`, `hRHS_b`, `ENNReal.add_lt_top` and
    -- `ENNReal.mul_lt_top`.
    -- =======================================================================
    obtain ⟨K, hKfin, hbound⟩ :
        ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
          ∫⁻ z in Metric.ball x₀ (4 * R₀), w z ^ (q + ε)
            ≤ K * (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q)
              + K * (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)) := by
      -- G2 — the Giaquinta–Giusti absorption, consuming the hole-filling
      -- inequality `holeFill` of the G1 node above through the iteration
      -- lemma `giaquinta_iteration`.
      -- =====================================================================
      -- RIGOROUS REDUCTION (fully discharged below): truncation + monotone
      -- convergence.  We reduce the target `hbound` for the genuine weight `w`
      -- to the SAME bound for the bounded truncations `w_N := min w N`,
      -- UNIFORMLY in `N`, via the monotone-convergence theorem.  Concretely:
      --   * `(min (w z) N)^{q+ε} ↑ (w z)^{q+ε}` pointwise as `N → ∞`
      --     (`min (w z) N ↑ w z`, and `·^{q+ε}` is monotone and continuous on
      --     `ℝ≥0∞`, so `iSup_eq_of_tendsto` gives the pointwise sup);
      --   * `lintegral_iSup'` exchanges the sup with `∫_{4B₀}`, identifying
      --     `∫_{4B₀} w^{q+ε} = ⨆ N, ∫_{4B₀} (min w N)^{q+ε}`;
      --   * with a single finite `K` for which every truncation obeys the
      --     bound (RHS independent of `N`), `iSup_le` collapses the sup.
      -- This isolates the analytic
      -- content into the per-`N` bounded absorbed bound `hboundN` below.
      -- =====================================================================
      -- Positivity of the reconstruction exponent (reused).
      have hqε0' : 0 ≤ q + ε := hqε0.le
      -- POINTWISE truncation sup of `Ž_N`: `⨆ N, w^q·(min (w z) N)^ε = w^{q+ε}`.
      have hptsup : ∀ z, ⨆ N : ℕ, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
          = w z ^ (q + ε) := by
        intro z
        -- `min (w z) ·` is monotone in the `ℕ`-truncation level.
        have hmin_mono : Monotone (fun n : ℕ => min (w z) (n : ℝ≥0∞)) := by
          intro a c hac; exact min_le_min_left _ (by exact_mod_cast hac)
        -- and its `ℕ`-sup is `w z` (the truncations exhaust `w z`).
        have hsup : ⨆ n : ℕ, min (w z) (n : ℝ≥0∞) = w z := by
          apply le_antisymm (iSup_le fun n => min_le_left _ _)
          apply le_of_forall_lt_imp_le_of_dense
          intro c hc
          obtain ⟨n, hn⟩ := exists_nat_gt c.toReal
          refine le_iSup_of_le n (le_min (le_of_lt hc) ?_)
          calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal (ne_top_of_lt hc)).symm
            _ ≤ ENNReal.ofReal n := ENNReal.ofReal_le_ofReal hn.le
            _ = (n : ℝ≥0∞) := by rw [ENNReal.ofReal_natCast]
        -- `w^q · (·)^ε` is monotone (exponent `≥ 0`) and continuous in the truncation.
        have hmono : Monotone (fun n : ℕ => w z ^ q * (min (w z) (n : ℝ≥0∞)) ^ ε) :=
          fun a c hac => mul_le_mul_right (ENNReal.rpow_le_rpow (hmin_mono hac) hεpos.le) _
        have htend : Tendsto (fun n : ℕ => min (w z) (n : ℝ≥0∞)) atTop (𝓝 (w z)) := by
          have h := tendsto_atTop_iSup hmin_mono; rwa [hsup] at h
        have hcompε : Tendsto (fun n : ℕ => (min (w z) (n : ℝ≥0∞)) ^ ε) atTop
            (𝓝 ((w z) ^ ε)) :=
          (ENNReal.continuous_rpow_const.tendsto (w z)).comp htend
        have hside : (w z) ^ ε ≠ 0 ∨ w z ^ q ≠ ⊤ := by
          rcases eq_or_ne (w z) 0 with hw0 | hw0
          · right; rw [hw0, ENNReal.zero_rpow_of_pos hq0']; simp
          · left; rw [ne_eq, ENNReal.rpow_eq_zero_iff]; push Not
            exact ⟨fun h => absurd h hw0, fun _ => hεpos.le⟩
        have hcomp : Tendsto (fun n : ℕ => w z ^ q * (min (w z) (n : ℝ≥0∞)) ^ ε) atTop
            (𝓝 (w z ^ q * (w z) ^ ε)) :=
          ENNReal.Tendsto.const_mul hcompε hside
        rw [show w z ^ q * w z ^ ε = w z ^ (q + ε) from
          (ENNReal.rpow_add_of_nonneg q ε hq0'.le hεpos.le).symm] at hcomp
        exact iSup_eq_of_tendsto hmono hcomp
      -- Per-truncation measurability and monotonicity for `lintegral_iSup'`.
      have hmeasN : ∀ N : ℕ,
          AEMeasurable (fun z => w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε)
            (volume.restrict (Metric.ball x₀ (4 * R₀))) :=
        fun N => (hwmeas.restrict.pow_const _).mul
          ((hwmeas.restrict.min aemeasurable_const).pow_const _)
      have hmonoN : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (4 * R₀))),
          Monotone (fun N : ℕ => w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε) := by
        filter_upwards with z a c hac
        exact mul_le_mul_right
          (ENNReal.rpow_le_rpow (min_le_min_left _ (by exact_mod_cast hac)) hεpos.le) _
      -- MONOTONE CONVERGENCE: identify the target LHS with the sup of truncations.
      have hMCT : ∫⁻ z in Metric.ball x₀ (4 * R₀), w z ^ (q + ε)
          = ⨆ N : ℕ, ∫⁻ z in Metric.ball x₀ (4 * R₀), w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε := by
        rw [← lintegral_iSup' hmeasN hmonoN]
        exact lintegral_congr_ae (by filter_upwards with z using (hptsup z).symm)
      -- =====================================================================
      -- G2 absorption — the per-`N` bounded bound, UNIFORM in `N`, PROVEN here
      -- from the hole-filling residual `holeFill` via the PROVEN Giaquinta–Giusti
      -- iteration lemma `giaquinta_iteration`.
      --
      -- For each truncation level `N`, the truncated mass `Z_N(t) =
      -- (∫_{ball x₀ t}(min w N)^{q+ε}).toReal` is finite (bounded by `N^{q+ε}·vol`),
      -- nonnegative, and bounded by `M_N` on `[4R₀,16R₀]`, and `holeFill` supplies
      -- the hole-filling inequality `Z_N(t) ≤ (κ·ε)·Z_N(s) + C₁·Wmaster/(s−t)² +
      -- C₁·Bmaster` for every `4R₀ ≤ t < s ≤ 16R₀`, with the absorbed
      -- coefficient `θ = κ·ε < 1`.  The iteration lemma then collapses the chain,
      -- giving `Z_N(4R₀) ≤ cIter·(C₁·Wmaster/(12R₀)² + C₁·Bmaster)`, which is a
      -- single FIXED `N`-independent ENNReal bound `K·∫_{16B₀}wᵠ + K·∫_{16B₀}b^{q+ε}`
      -- after converting `Wmaster, Bmaster` back to their (finite) lintegrals.  The
      -- monotone-convergence collapse `hMCT` then removes the truncation.
      --
      -- The PROVEN Giaquinta–Giusti iteration constant `c = c(α, θ)` for `α = 2`,
      -- `θ = κ·ε < 1` (honest by `hθε`).  It depends only on `α, θ`, i.e. on `q, A, ε`.
      obtain ⟨cIter, hcIter0, hcIter⟩ := giaquinta_iteration (α := (2 : ℝ)) (θ := κ * ε)
        (by norm_num) hκε0 hθε
      -- Geometry: `12 R₀ = 16R₀ − 4R₀ > 0` and `(12R₀)² > 0`.
      have h12R₀ : (0 : ℝ) < 12 * R₀ := by linarith
      have hgapα : (0 : ℝ) < (16 * R₀ - 4 * R₀) ^ (2 : ℝ) := by
        have : (16 * R₀ - 4 * R₀) = 12 * R₀ := by ring
        rw [this]; exact Real.rpow_pos_of_pos h12R₀ 2
      -- The single finite, `N`-independent coefficient `K`.
      set K : ℝ≥0∞ := ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ)) +
                ENNReal.ofReal (cIter * C₁) with hKdef
      have hKfin : K ≠ ⊤ := by
        rw [hKdef]
        exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
      have hboundN : ∀ N : ℕ,
          ∫⁻ z in Metric.ball x₀ (4 * R₀), w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
            ≤ K * (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q)
              + K * (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)) := by
        intro N
        -- `∫_{16B₀} w^q < ⊤` (master finiteness, from `hWmaster`).
        have hW16fin : ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q < ⊤ := hWmaster
        -- Per-`N` bound: `Ž_N(s) = ∫_{B_s} w^q·(min w N)^ε ≤ N^ε·∫_{16B₀} w^q` (`s ≤ 16R₀`).
        have hNbound : ∀ s : ℝ, s ≤ 16 * R₀ →
            ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
              ≤ (N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q := by
          intro s hs16
          calc ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
              ≤ ∫⁻ z in Metric.ball x₀ s, w z ^ q * (N : ℝ≥0∞) ^ ε := by
                apply lintegral_mono; intro z
                exact mul_le_mul_right (ENNReal.rpow_le_rpow (min_le_right _ _) hεpos.le) _
            _ = (N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ s, w z ^ q := by
                rw [← lintegral_const_mul' _ _ (by
                  exact (ENNReal.rpow_lt_top_of_nonneg hεpos.le (ENNReal.natCast_ne_top N)).ne)]
                apply lintegral_congr_ae; filter_upwards with z; rw [mul_comm]
            _ ≤ (N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q :=
                mul_le_mul_right (lintegral_mono_set (Metric.ball_subset_ball hs16)) _
        have hNfin : ∀ s : ℝ, s ≤ 16 * R₀ →
            ∫⁻ z in Metric.ball x₀ s, w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε < ⊤ := by
          intro s hs16
          refine lt_of_le_of_lt (hNbound s hs16) ?_
          exact ENNReal.mul_lt_top
            (ENNReal.rpow_lt_top_of_nonneg hεpos.le (ENNReal.natCast_ne_top N)) hW16fin
        -- The real-valued `Ž_N`.
        set ZN : ℝ → ℝ := fun t => (∫⁻ z in Metric.ball x₀ t,
          w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε).toReal with hZNdef
        have hZN0 : ∀ t ∈ Set.Icc (4 * R₀) (16 * R₀), 0 ≤ ZN t :=
          fun t _ => ENNReal.toReal_nonneg
        -- The uniform bound `M_N` on `[4R₀, 16R₀]` (`Ž_N(t) ≤ N^ε·∫_{16B₀}w^q` for `t ≤ 16R₀`).
        set MN : ℝ :=
          ((N : ℝ≥0∞) ^ ε * ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q).toReal with hMNdef
        have hZNbdd : ∀ t ∈ Set.Icc (4 * R₀) (16 * R₀), ZN t ≤ MN := by
          intro t ht
          rw [hZNdef, hMNdef]
          apply ENNReal.toReal_mono
          · exact ENNReal.mul_ne_top (ENNReal.rpow_lt_top_of_nonneg hεpos.le
              (ENNReal.natCast_ne_top N)).ne hW16fin.ne
          · exact hNbound t ht.2
        -- Apply the iteration lemma.
        have hZNiter := hcIter (Z := ZN) (r := 4 * R₀) (R := 16 * R₀)
          (A := C₁ * Wmaster) (B := C₁ * Bmaster) (M := MN)
          (by linarith) (mul_nonneg hC₁0 hWmaster0) (mul_nonneg hC₁0 hBmaster0)
          hZN0 hZNbdd
          (fun t s ht hts hs => by
            have := holeFill N t s ht hts hs
            simpa only [hZNdef] using this)
        -- `hZNiter : ZN (4R₀) ≤ cIter * (C₁ * Wmaster / (16R₀ - 4R₀)^2 + C₁ * Bmaster)`.
        -- Convert the LHS `ZN (4R₀)` back to the ENNReal target.
        have hround : ∫⁻ z in Metric.ball x₀ (4 * R₀), w z ^ q * (min (w z) (N : ℝ≥0∞)) ^ ε
            = ENNReal.ofReal (ZN (4 * R₀)) := by
          rw [hZNdef, ENNReal.ofReal_toReal (hNfin (4 * R₀) (by linarith)).ne]
        rw [hround]
        -- RHS bound in ℝ.
        have hRHSreal : ZN (4 * R₀)
            ≤ cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ) * Wmaster + cIter * C₁ * Bmaster := by
          calc ZN (4 * R₀)
              ≤ cIter * (C₁ * Wmaster / (16 * R₀ - 4 * R₀) ^ (2 : ℝ) + C₁ * Bmaster) := hZNiter
            _ = cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ) * Wmaster + cIter * C₁ * Bmaster := by
                rw [mul_add, mul_div_assoc']; ring
        -- The two master masses as ENNReal `ofReal` of their `.toReal`.
        have hWeq : ENNReal.ofReal Wmaster = ∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q := by
          rw [hWmasterdef, ENNReal.ofReal_toReal hWmaster.ne]
        have hBeq : ENNReal.ofReal Bmaster = ∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε) := by
          rw [hBmasterdef, ENNReal.ofReal_toReal hBmaster.ne]
        -- Assemble the ENNReal bound.
        calc ENNReal.ofReal (ZN (4 * R₀))
            ≤ ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ) * Wmaster
                + cIter * C₁ * Bmaster) := ENNReal.ofReal_le_ofReal hRHSreal
          _ = ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ) * Wmaster)
                + ENNReal.ofReal (cIter * C₁ * Bmaster) := by
                rw [ENNReal.ofReal_add (by positivity) (by positivity)]
          _ = ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ)) * ENNReal.ofReal Wmaster
                + ENNReal.ofReal (cIter * C₁) * ENNReal.ofReal Bmaster := by
                rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ))
                * (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q)
                + ENNReal.ofReal (cIter * C₁)
                    * (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)) := by
                rw [hWeq, hBeq]
          _ ≤ (ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ))
                  + ENNReal.ofReal (cIter * C₁))
                * (∫⁻ z in Metric.ball x₀ (16 * R₀), w z ^ q)
                + (ENNReal.ofReal (cIter * C₁ / (16 * R₀ - 4 * R₀) ^ (2 : ℝ))
                    + ENNReal.ofReal (cIter * C₁))
                * (∫⁻ z in Metric.ball x₀ (16 * R₀), b z ^ (q + ε)) := by
                gcongr <;> simp
      -- Collapse the monotone sup against the `N`-uniform bound.
      exact ⟨K, hKfin, by rw [hMCT]; exact iSup_le hboundN⟩
    refine lt_of_le_of_lt hbound (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact ENNReal.mul_lt_top (lt_of_le_of_ne le_top hKfin) hRHS_w
    · exact ENNReal.mul_lt_top (lt_of_le_of_ne le_top hKfin) hRHS_b
  exact absorb


end NoWanderingDomains
