/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Geometric
import NoWanderingDomains.QC.Calculus.AnalyticClosedness
import NoWanderingDomains.QC.Regularity.Quasisymmetry
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Compactness.CompactlyCoherentSpace
import Mathlib.Topology.Sequences
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Quasiconformal calculus: compactness

Geometric quasiconformality is closed under locally uniform limits, and normalized uniformly
`K`-quasiconformal families are normal:

* **Normal-family compactness** (`exists_subseq_tendstoLocallyUniformly_isQCGeometric`) — a
  two-point–normalized sequence of geometric `K`-quasiconformal maps (`fₙ p = a`, `fₙ q = b` with
  `p ≠ q` and `a ≠ b`) has a subsequence converging locally uniformly to a geometric
  `K`-quasiconformal limit. The two-value normalization supplies equicontinuity of the family and of
  its inverses together with pointwise bounds; an Arzelà–Ascoli extraction then yields locally
  uniform limits of the maps and of their inverses, the limit is a homeomorphism, and the
  analytic-route closedness theorem
  (`isQCGeometric_of_tendstoLocallyUniformly_inverse`, `QC/Calculus/AnalyticClosedness.lean`)
  makes it `K`-quasiconformal.

The file also proves a standalone structural fact:

* `sensePreserving_of_tendstoLocallyUniformly` — the topological orientation (`SensePreserving`)
  passes to a homeomorphic locally uniform limit, since the image circles converge uniformly to a
  loop bounded away from the centre, so the winding `+1` (continuous-log increment `2π i`) is
  transported by homotopy invariance.

The extraction rests on `pointwise_bounded_of_equicontinuousOn` for the pointwise bounds, the
Arzelà–Ascoli step `exists_subseq_tendsto_continuousMap` in `C(ℂ, ℂ)`, and
`isHomeomorph_of_tendstoLocallyUniformly_inverse` for identifying the limit as a homeomorphism.
-/

open Filter Set Metric Topology
open scoped ENNReal Topology

namespace NoWanderingDomains

/-- **Orientation passes to locally uniform limits.** A homeomorphism `g` that is a locally uniform
limit of topologically sense-preserving maps `fₙ` is itself sense-preserving. For a centre `z₀` and
radius `r`, the image circles `θ ↦ fₙ (z₀ + r e^{iθ}) - fₙ z₀` converge uniformly on `[0, 2π]` to
`θ ↦ g (z₀ + r e^{iθ}) - g z₀`, which is continuous and (since `g` is injective) bounded away from
`0`; eventually each `fₙ` circle is homotopic in `ℂ ∖ {0}` to the `g` circle by the straight-line
homotopy, so the winding `+1` of the `fₙ` circles (continuous-log increment `2π i`) transfers to
`g`. -/
theorem sensePreserving_of_tendstoLocallyUniformly {fₙ : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ n, SensePreserving (fₙ n)) (hconv : TendstoLocallyUniformly fₙ g atTop)
    (hg : IsHomeomorph g) : SensePreserving g := by
  classical
  refine ⟨hg, ?_⟩
  -- Notation and basic positivity.
  set τ : ℝ := 2 * Real.pi with hτ_def
  have hτ_pos : 0 < τ := by rw [hτ_def]; positivity
  have hτ_nonneg : (0 : ℝ) ≤ τ := hτ_pos.le
  have h2pi_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hg_inj : Function.Injective g := hg.injective
  have hg_cont : Continuous g := hg.continuous
  have hfn_inj : ∀ n, Function.Injective (fₙ n) := fun n => (hf n).1.injective
  have hfn_cont : ∀ n, Continuous (fₙ n) := fun n => (hf n).1.continuous
  ----------------------------------------------------------------------------
  -- Helper: well-definedness of the increment of a continuous log lift on `[0, τ]`.
  ----------------------------------------------------------------------------
  have helperW : ∀ (L₁ L₂ : ℝ → ℂ), Continuous L₁ → Continuous L₂ →
      (∀ t ∈ Set.Icc (0 : ℝ) τ, Complex.exp (L₁ t) = Complex.exp (L₂ t)) →
      L₁ τ - L₁ 0 = L₂ τ - L₂ 0 := by
    intro L₁ L₂ hL₁ hL₂ hexp
    set d : ℝ → ℂ := fun t => L₁ t - L₂ t with hd
    have hdcont : Continuous d := hL₁.sub hL₂
    have hdK : ∀ t ∈ Set.Icc (0 : ℝ) τ,
        ∃ K : ℤ, d t = (K : ℂ) * (2 * Real.pi * Complex.I) := by
      intro t ht
      refine (Complex.exp_eq_one_iff).mp ?_
      simp only [hd, Complex.exp_sub, hexp t ht, div_self (Complex.exp_ne_zero _)]
    set wfun : ℝ → ℤ :=
      fun t => if h : t ∈ Set.Icc (0 : ℝ) τ then (hdK t h).choose else 0 with hwf
    have hwf_spec : ∀ t ∈ Set.Icc (0 : ℝ) τ,
        d t = ((wfun t : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      intro t ht; simp only [hwf, dif_pos ht]; exact (hdK t ht).choose_spec
    have hwf_cont : ContinuousOn (fun t => ((wfun t : ℤ) : ℂ)) (Set.Icc (0 : ℝ) τ) := by
      have heq : Set.EqOn (fun t => ((wfun t : ℤ) : ℂ))
          (fun t => d t / (2 * Real.pi * Complex.I)) (Set.Icc (0 : ℝ) τ) := by
        intro t ht
        simp only
        rw [hwf_spec t ht, mul_div_assoc, div_self h2pi_ne, mul_one]
      exact ContinuousOn.congr (hdcont.continuousOn.div_const _) heq
    have hwf_int_cont : ContinuousOn wfun (Set.Icc (0 : ℝ) τ) := by
      rw [continuousOn_iff_continuous_domRestrict] at hwf_cont ⊢
      exact Complex.isClosedEmbedding_intCast.isEmbedding.continuous_iff.mpr hwf_cont
    have hconst : wfun 0 = wfun τ :=
      isPreconnected_Icc.constant hwf_int_cont ⟨le_refl _, hτ_nonneg⟩ ⟨hτ_nonneg, le_refl _⟩
    have hdd : d τ = d 0 := by
      rw [hwf_spec τ ⟨hτ_nonneg, le_refl _⟩, hwf_spec 0 ⟨le_refl _, hτ_nonneg⟩, hconst]
    simp only [hd] at hdd
    linear_combination hdd
  ----------------------------------------------------------------------------
  -- The homotopy engine: a jointly continuous nonvanishing family of loops over
  -- `[α, β] × [0, τ]` transports a winding-`+1` continuous log on `[0, τ]` of the
  -- `α`-slice to a winding-`+1` continuous log on `[0, τ]` of the `β`-slice.
  ----------------------------------------------------------------------------
  have engine : ∀ (α β : ℝ) (F : ℝ → ℝ → ℂ), α ≤ β →
      ContinuousOn (Function.uncurry F) (Set.Icc α β ×ˢ Set.Icc (0 : ℝ) τ) →
      (∀ s ∈ Set.Icc α β, ∀ θ ∈ Set.Icc (0 : ℝ) τ, F s θ ≠ 0) →
      (∀ s ∈ Set.Icc α β, F s 0 = F s τ) →
      ∀ (L₀ : ℝ → ℂ), Continuous L₀ →
        (∀ θ ∈ Set.Icc (0 : ℝ) τ, Complex.exp (L₀ θ) = F α θ) →
        L₀ τ - L₀ 0 = 2 * (Real.pi : ℂ) * Complex.I →
      ∃ Lβ : ℝ → ℂ, Continuous Lβ ∧
        (∀ θ ∈ Set.Icc (0 : ℝ) τ, Complex.exp (Lβ θ) = F β θ) ∧
        Lβ τ - Lβ 0 = 2 * (Real.pi : ℂ) * Complex.I := by
    intro α β F hαβ hFcont hFne hFloop L₀ hL₀c hL₀e hL₀incr
    have hα_mem : α ∈ Set.Icc α β := ⟨le_refl _, hαβ⟩
    have hβ_mem : β ∈ Set.Icc α β := ⟨hαβ, le_refl _⟩
    -- Parametric continuous log lift Λ of F over the rectangle.
    obtain ⟨Λ, hΛc, hΛe⟩ :=
      continuous_log_lift_param_of_continuous_ne_zero hαβ hτ_nonneg F hFcont hFne
    -- Increment of the slice loop is continuous in s and an integer multiple of 2πi.
    set W : ℝ → ℂ := fun s => Λ s τ - Λ s 0 with hW_def
    have hWcont : Continuous W := by
      refine Continuous.sub ?_ ?_
      · exact hΛc.comp (continuous_id.prodMk continuous_const)
      · exact hΛc.comp (continuous_id.prodMk continuous_const)
    have hWexp : ∀ s ∈ Set.Icc α β, Complex.exp (W s) = 1 := by
      intro s hs
      have h0 := hΛe s hs 0 ⟨le_refl _, hτ_nonneg⟩
      have hτ := hΛe s hs τ ⟨hτ_nonneg, le_refl _⟩
      simp only [hW_def, Complex.exp_sub, hτ, h0]
      rw [← hFloop s hs, div_self (hFne s hs 0 ⟨le_refl _, hτ_nonneg⟩)]
    have hWK : ∀ s ∈ Set.Icc α β,
        ∃ K : ℤ, W s = (K : ℂ) * (2 * Real.pi * Complex.I) :=
      fun s hs => (Complex.exp_eq_one_iff).mp (hWexp s hs)
    set kfun : ℝ → ℤ :=
      fun s => if h : s ∈ Set.Icc α β then (hWK s h).choose else 0 with hkf
    have hkf_spec : ∀ s ∈ Set.Icc α β,
        W s = ((kfun s : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      intro s hs; simp only [hkf, dif_pos hs]; exact (hWK s hs).choose_spec
    have hkf_cont : ContinuousOn (fun s => ((kfun s : ℤ) : ℂ)) (Set.Icc α β) := by
      have heq : Set.EqOn (fun s => ((kfun s : ℤ) : ℂ))
          (fun s => W s / (2 * Real.pi * Complex.I)) (Set.Icc α β) := by
        intro s hs
        simp only
        rw [hkf_spec s hs, mul_div_assoc, div_self h2pi_ne, mul_one]
      exact ContinuousOn.congr (hWcont.continuousOn.div_const _) heq
    have hkf_int_cont : ContinuousOn kfun (Set.Icc α β) := by
      rw [continuousOn_iff_continuous_domRestrict] at hkf_cont ⊢
      exact Complex.isClosedEmbedding_intCast.isEmbedding.continuous_iff.mpr hkf_cont
    have hkconst : kfun α = kfun β :=
      isPreconnected_Icc.constant hkf_int_cont hα_mem hβ_mem
    -- At s = α the increment is 2πi (by well-definedness against the input log).
    have hWα : W α = 2 * (Real.pi : ℂ) * Complex.I := by
      have hΛα_c : Continuous (fun θ => Λ α θ) := hΛc.comp (continuous_const.prodMk continuous_id)
      have hmatch : ∀ θ ∈ Set.Icc (0 : ℝ) τ,
          Complex.exp (L₀ θ) = Complex.exp (Λ α θ) := by
        intro θ hθ
        rw [hL₀e θ hθ, hΛe α hα_mem θ hθ]
      have := helperW L₀ (fun θ => Λ α θ) hL₀c hΛα_c hmatch
      rw [hL₀incr] at this
      rw [hW_def]; exact this.symm
    have hWβ : W β = 2 * (Real.pi : ℂ) * Complex.I := by
      rw [hkf_spec β hβ_mem, ← hkconst, ← hkf_spec α hα_mem, hWα]
    refine ⟨fun θ => Λ β θ, hΛc.comp (continuous_const.prodMk continuous_id), ?_, ?_⟩
    · intro θ hθ; exact hΛe β hβ_mem θ hθ
    · simpa only [hW_def] using hWβ
  ----------------------------------------------------------------------------
  -- Global log lift: extend a winding-`+1` log on `[0, τ]` of a continuous,
  -- nonvanishing, `τ`-periodic loop `F` to all of `ℝ`.
  ----------------------------------------------------------------------------
  have hfact : Fact ((0 : ℝ) < τ) := ⟨hτ_pos⟩
  have globalLog : ∀ (F : ℝ → ℂ), Continuous F → (∀ θ, F θ ≠ 0) →
      Function.Periodic F τ →
      ∀ (L₀ : ℝ → ℂ), Continuous L₀ →
        (∀ θ ∈ Set.Icc (0 : ℝ) τ, Complex.exp (L₀ θ) = F θ) →
        L₀ τ - L₀ 0 = 2 * (Real.pi : ℂ) * Complex.I →
      ∃ L : ℝ → ℂ, Continuous L ∧
        (∀ θ : ℝ, Complex.exp (L θ) = F θ) ∧
        L τ - L 0 = 2 * (Real.pi : ℂ) * Complex.I := by
    intro F hFc hFne hFper L₀ hL₀c hL₀e hL₀incr
    -- The "untwisted" loop M θ = L₀ θ - θ i is periodic-compatible at the endpoints.
    set M : ℝ → ℂ := fun θ => L₀ θ - (θ : ℂ) * Complex.I with hM_def
    have hMc : Continuous M := by
      refine hL₀c.sub ?_
      exact (Complex.continuous_ofReal.mul continuous_const)
    have hM_endpoints : M 0 = M τ := by
      simp only [hM_def, hτ_def]
      have : L₀ (2 * Real.pi) - L₀ 0 = 2 * (Real.pi : ℂ) * Complex.I := by
        rw [← hτ_def]; exact hL₀incr
      push_cast
      linear_combination -this
    -- Periodic continuous extension via the additive circle.
    set Mt : ℝ → ℂ := fun θ => AddCircle.liftIco τ 0 M (↑θ) with hMt_def
    have hMt_cont : Continuous Mt := by
      have hlift : Continuous (AddCircle.liftIco τ 0 M) :=
        AddCircle.liftIco_zero_continuous hM_endpoints hMc.continuousOn
      exact hlift.comp (AddCircle.continuous_mk' τ)
    have hMt_per : Function.Periodic Mt τ := by
      intro θ
      simp only [hMt_def]
      rw [AddCircle.coe_add_period]
    have hMt_eq_Ico : ∀ θ ∈ Set.Ico (0 : ℝ) τ, Mt θ = M θ := by
      intro θ hθ
      simp only [hMt_def]
      exact AddCircle.liftIco_zero_coe_apply hθ
    -- The candidate global log.
    set L : ℝ → ℂ := fun θ => Mt θ + (θ : ℂ) * Complex.I with hL_def
    have hLc : Continuous L :=
      hMt_cont.add (Complex.continuous_ofReal.mul continuous_const)
    -- exp(L θ) = F θ for all θ, via periodicity of both sides and agreement on [0, τ).
    have hE_per : Function.Periodic (fun θ => Complex.exp (L θ)) τ := by
      intro θ
      simp only [hL_def]
      rw [hMt_per θ]
      rw [show ((θ + τ : ℝ) : ℂ) * Complex.I
            = (θ : ℂ) * Complex.I + ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
            simp only [hτ_def]; push_cast; ring]
      rw [show Mt θ + ((θ : ℂ) * Complex.I + ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
            = (Mt θ + (θ : ℂ) * Complex.I) + ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
            ring]
      rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hE_eq_Ico : ∀ θ ∈ Set.Ico (0 : ℝ) τ, Complex.exp (L θ) = F θ := by
      intro θ hθ
      have hθ_Icc : θ ∈ Set.Icc (0 : ℝ) τ := ⟨hθ.1, hθ.2.le⟩
      simp only [hL_def]
      rw [hMt_eq_Ico θ hθ]
      simp only [hM_def]
      rw [show L₀ θ - (θ : ℂ) * Complex.I + (θ : ℂ) * Complex.I = L₀ θ by ring]
      exact hL₀e θ hθ_Icc
    have hL_exp : ∀ θ : ℝ, Complex.exp (L θ) = F θ := by
      intro θ
      -- Reduce θ to the fundamental domain [0, τ) by subtracting ⌊θ/τ⌋·τ.
      set n : ℤ := ⌊θ / τ⌋ with hn_def
      set θ₀ : ℝ := θ - (n : ℝ) * τ with hθ₀_def
      have hfloor_le : (n : ℝ) * τ ≤ θ := by
        rw [hn_def]
        have h := Int.floor_le (θ / τ)
        rw [le_div_iff₀ hτ_pos] at h
        linarith [h]
      have hfloor_lt : θ < ((n : ℝ) + 1) * τ := by
        rw [hn_def]
        have h := Int.lt_floor_add_one (θ / τ)
        rw [div_lt_iff₀ hτ_pos] at h
        linarith [h]
      have hθ₀_Ico : θ₀ ∈ Set.Ico (0 : ℝ) τ := by
        rw [hθ₀_def]
        refine ⟨by linarith, by nlinarith [hfloor_lt]⟩
      have hLθ : Complex.exp (L θ) = Complex.exp (L θ₀) := by
        have h := (hE_per.sub_int_mul_eq (x := θ) n)
        rw [← hθ₀_def] at h
        exact h.symm
      have hFθ : F θ₀ = F θ := by
        have h := (hFper.sub_int_mul_eq (x := θ) n)
        rw [← hθ₀_def] at h
        exact h
      rw [hLθ, hE_eq_Ico θ₀ hθ₀_Ico, hFθ]
    refine ⟨L, hLc, hL_exp, ?_⟩
    -- The increment over [0, τ].
    have h0 : L 0 = Mt 0 := by simp [hL_def]
    have hτv : L τ = Mt τ + (τ : ℂ) * Complex.I := by simp [hL_def]
    have hMt_0τ : Mt τ = Mt 0 := by
      have := hMt_per 0; simpa using this
    rw [hτv, h0, hMt_0τ]
    simp only [hτ_def]
    push_cast; ring
  ----------------------------------------------------------------------------
  -- Reduce to a.e. centres at which EVERY `fₙ` satisfies its winding clause.
  ----------------------------------------------------------------------------
  have hae : ∀ᵐ z₀ : ℂ, ∀ n : ℕ, ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      ∃ L : ℝ → ℂ, Continuous L ∧
        (∀ θ : ℝ, Complex.exp (L θ)
          = fₙ n (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - fₙ n z₀) ∧
        L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I := by
    rw [MeasureTheory.ae_all_iff]
    exact fun n => (hf n).2
  filter_upwards [hae] with z₀ hz₀
  -- The point map `θ ↦ z₀ + r e^{iθ}`.
  -- It suffices to produce the winding lift for every `r > 0`.
  refine Filter.eventually_of_mem self_mem_nhdsWithin ?_
  intro r hr
  have hr_pos : 0 < r := hr
  -- Abbreviation for the image circle of a map `h` at radius `r`.
  set P : ℝ → ℂ := fun θ => z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hP_def
  have hP_cont : Continuous P := by
    refine continuous_const.add ?_
    exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  have hP_ne_z₀ : ∀ θ : ℝ, P θ ≠ z₀ := by
    intro θ hθ
    have h1 : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = 0 := by
      have := hθ; simp only [hP_def] at this; linear_combination this
    have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr_pos
    exact (mul_ne_zero hr_ne (Complex.exp_ne_zero _)) h1
  have hP_per : ∀ θ : ℝ, P (θ + 2 * Real.pi) = P θ := by
    intro θ
    simp only [hP_def]
    congr 2
    rw [show ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
          = (θ : ℂ) * Complex.I + ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
          push_cast; ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  -- The image circle of `h` at radius `r`.
  set C : (ℂ → ℂ) → ℝ → ℂ := fun h θ => h (P θ) - h z₀ with hC_def
  have hC_cont : ∀ (h : ℂ → ℂ), Continuous h → Continuous (C h) := by
    intro h hh
    exact (hh.comp hP_cont).sub continuous_const
  have hC_per : ∀ (h : ℂ → ℂ), ∀ θ : ℝ, C h (θ + 2 * Real.pi) = C h θ := by
    intro h θ; simp only [hC_def]; rw [hP_per θ]
  have hC_loop : ∀ (h : ℂ → ℂ), C h 0 = C h τ := by
    intro h
    have := hC_per h 0
    simpa [hτ_def] using this.symm
  ----------------------------------------------------------------------------
  -- Step (a): each `fₙ` image circle winds `+1` at the fixed radius `r`.
  ----------------------------------------------------------------------------
  have step_fn : ∀ n : ℕ, ∃ Lr : ℝ → ℂ, Continuous Lr ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) τ, Complex.exp (Lr θ) = C (fₙ n) θ) ∧
      Lr τ - Lr 0 = 2 * (Real.pi : ℂ) * Complex.I := by
    intro n
    -- Choose a small radius `ρ ∈ (0, r]` admitting the winding clause for `fₙ n`.
    obtain ⟨ρ, ⟨Lρ, hLρc, hLρe, hLρincr⟩, hρ_mem⟩ :=
      (((hz₀ n).and_frequently
        (Filter.Eventually.frequently (Ioc_mem_nhdsGT hr_pos))).exists)
    obtain ⟨hρ_pos, hρ_le⟩ := hρ_mem
    -- The radius homotopy family for `fₙ n`.
    set Fr : ℝ → ℝ → ℂ := fun s θ =>
      fₙ n (z₀ + (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - fₙ n z₀ with hFr_def
    have hFr_cont : ContinuousOn (Function.uncurry Fr)
        (Set.Icc ρ r ×ˢ Set.Icc (0 : ℝ) τ) := by
      refine Continuous.continuousOn ?_
      change Continuous fun p : ℝ × ℝ =>
        fₙ n (z₀ + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) - fₙ n z₀
      refine ((hfn_cont n).comp ?_).sub continuous_const
      refine continuous_const.add ?_
      refine Continuous.mul ?_ ?_
      · exact Complex.continuous_ofReal.comp continuous_fst
      · exact Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    have hFr_ne : ∀ s ∈ Set.Icc ρ r, ∀ θ ∈ Set.Icc (0 : ℝ) τ, Fr s θ ≠ 0 := by
      intro s hs θ _ hzero
      have hs_pos : 0 < s := lt_of_lt_of_le hρ_pos hs.1
      have hs_ne : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs_pos
      have hpt_ne : z₀ + (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ≠ z₀ := by
        intro hpt
        have : (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = 0 := by linear_combination hpt
        exact (mul_ne_zero hs_ne (Complex.exp_ne_zero _)) this
      have : fₙ n (z₀ + (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = fₙ n z₀ := by
        simp only [hFr_def] at hzero; linear_combination hzero
      exact hpt_ne (hfn_inj n this)
    have hFr_loop : ∀ s ∈ Set.Icc ρ r, Fr s 0 = Fr s τ := by
      intro s _
      simp only [hFr_def, hτ_def]
      have he0 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by
        rw [show ((0 : ℝ) : ℂ) = 0 by push_cast; ring, zero_mul, Complex.exp_zero]
      have heτ : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
        rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I
              = ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
        exact Complex.exp_int_mul_two_pi_mul_I 1
      rw [he0, heτ]
    -- The input log at radius `ρ` (restricted to `[0, τ]`).
    have hLρe' : ∀ θ ∈ Set.Icc (0 : ℝ) τ, Complex.exp (Lρ θ) = Fr ρ θ :=
      fun θ _ => hLρe θ
    have hLρincr' : Lρ τ - Lρ 0 = 2 * (Real.pi : ℂ) * Complex.I := by
      rw [hτ_def]; exact hLρincr
    obtain ⟨Lr, hLrc, hLre, hLrincr⟩ :=
      engine ρ r Fr hρ_le hFr_cont hFr_ne hFr_loop Lρ hLρc hLρe' hLρincr'
    refine ⟨Lr, hLrc, ?_, hLrincr⟩
    intro θ hθ
    rw [hLre θ hθ]
  ----------------------------------------------------------------------------
  -- Step (b): the `g` image circle is bounded below away from `0`.
  ----------------------------------------------------------------------------
  have hCg_cont : Continuous (C g) := hC_cont g hg_cont
  have hCg_ne : ∀ θ : ℝ, C g θ ≠ 0 := by
    intro θ hθ
    have : g (P θ) = g z₀ := by simp only [hC_def] at hθ; linear_combination hθ
    exact hP_ne_z₀ θ (hg_inj this)
  obtain ⟨θm, _, hθm⟩ :=
    isCompact_Icc.exists_isMinOn (s := Set.Icc (0 : ℝ) τ) ⟨0, ⟨le_refl _, hτ_nonneg⟩⟩
      (hCg_cont.norm.continuousOn)
  set m : ℝ := ‖C g θm‖ with hm_def
  have hm_pos : 0 < m := norm_pos_iff.mpr (hCg_ne θm)
  have hm_lb : ∀ θ ∈ Set.Icc (0 : ℝ) τ, m ≤ ‖C g θ‖ := fun θ hθ => hθm hθ
  ----------------------------------------------------------------------------
  -- Step (c): uniform convergence of the `fₙ` circles to the `g` circle.
  ----------------------------------------------------------------------------
  -- Uniform convergence on the compact image circle `K = P '' [0, τ]`.
  set K : Set ℂ := P '' Set.Icc (0 : ℝ) τ with hK_def
  have hK_compact : IsCompact K :=
    (isCompact_Icc.image hP_cont)
  have hunifK : TendstoUniformlyOn fₙ g atTop K := by
    rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK_compact]
    exact (hconv.tendstoLocallyUniformlyOn)
  rw [Metric.tendstoUniformlyOn_iff] at hunifK
  -- Pointwise convergence at the centre `z₀`.
  have htend_z₀ : Filter.Tendsto (fun n => fₙ n z₀) atTop (𝓝 (g z₀)) := by
    have hloc : TendstoLocallyUniformlyOn fₙ g atTop Set.univ :=
      tendstoLocallyUniformlyOn_univ.mpr hconv
    exact hloc.tendsto_at (Set.mem_univ z₀)
  rw [Metric.tendsto_atTop] at htend_z₀
  -- Eventually, the `fₙ` circle is within `m` of the `g` circle on `[0, τ]`.
  have hclose : ∀ᶠ n in atTop, ∀ θ ∈ Set.Icc (0 : ℝ) τ, ‖C g θ - C (fₙ n) θ‖ < m := by
    obtain ⟨N₁, hN₁⟩ := htend_z₀ (m / 2) (by positivity)
    have hK := hunifK (m / 2) (by positivity)
    filter_upwards [hK, Filter.eventually_ge_atTop N₁] with n hn hnN₁
    intro θ hθ
    have hPθ_K : P θ ∈ K := ⟨θ, hθ, rfl⟩
    have h1 : dist (g (P θ)) (fₙ n (P θ)) < m / 2 := hn (P θ) hPθ_K
    have h2 : dist (g z₀) (fₙ n z₀) < m / 2 := by
      have := hN₁ n hnN₁; rwa [dist_comm] at this
    have hsplit : C g θ - C (fₙ n) θ
        = (g (P θ) - fₙ n (P θ)) - (g z₀ - fₙ n z₀) := by
      simp only [hC_def]; ring
    rw [hsplit]
    calc ‖(g (P θ) - fₙ n (P θ)) - (g z₀ - fₙ n z₀)‖
        ≤ ‖g (P θ) - fₙ n (P θ)‖ + ‖g z₀ - fₙ n z₀‖ := norm_sub_le _ _
      _ < m / 2 + m / 2 := by
          rw [← Complex.dist_eq, ← Complex.dist_eq]; exact add_lt_add h1 h2
      _ = m := by ring
  ----------------------------------------------------------------------------
  -- Step (d): transfer the winding `+1` from `fₙ` to `g` via the line homotopy.
  ----------------------------------------------------------------------------
  obtain ⟨n, hn_close⟩ := hclose.exists
  obtain ⟨Lfn, hLfnc, hLfne, hLfnincr⟩ := step_fn n
  -- The straight-line homotopy between the `fₙ` circle and the `g` circle.
  set G : ℝ → ℝ → ℂ := fun s θ => (1 - (s : ℂ)) * C (fₙ n) θ + (s : ℂ) * C g θ with hG_def
  have hG_cont : ContinuousOn (Function.uncurry G) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) τ) := by
    refine Continuous.continuousOn ?_
    change Continuous fun p : ℝ × ℝ => (1 - (p.1 : ℂ)) * C (fₙ n) p.2 + (p.1 : ℂ) * C g p.2
    refine Continuous.add ?_ ?_
    · exact (continuous_const.sub (Complex.continuous_ofReal.comp continuous_fst)).mul
        ((hC_cont (fₙ n) (hfn_cont n)).comp continuous_snd)
    · exact (Complex.continuous_ofReal.comp continuous_fst).mul (hCg_cont.comp continuous_snd)
  have hG_ne : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ θ ∈ Set.Icc (0 : ℝ) τ, G s θ ≠ 0 := by
    intro s hs θ hθ
    have hrw : G s θ = C g θ + (1 - (s : ℝ) : ℂ) * (C (fₙ n) θ - C g θ) := by
      simp only [hG_def]; ring
    have hclose_θ : ‖C g θ - C (fₙ n) θ‖ < m := hn_close θ hθ
    have hdiff : ‖C (fₙ n) θ - C g θ‖ < m := by rw [norm_sub_rev]; exact hclose_θ
    have hcoeff : ‖(1 - (s : ℝ) : ℂ)‖ ≤ 1 := by
      rw [show ((1 - (s : ℝ) : ℂ)) = ((1 - s : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by linarith [hs.2])]
      linarith [hs.1]
    have hgθ : m ≤ ‖C g θ‖ := hm_lb θ hθ
    -- The perturbation term has norm < m, hence cannot cancel C g θ (norm ≥ m).
    have hpert_lt : ‖(1 - (s : ℝ) : ℂ) * (C (fₙ n) θ - C g θ)‖ < m := by
      rw [norm_mul]
      calc ‖(1 - (s : ℝ) : ℂ)‖ * ‖C (fₙ n) θ - C g θ‖
          ≤ 1 * ‖C (fₙ n) θ - C g θ‖ :=
            mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
        _ = ‖C (fₙ n) θ - C g θ‖ := one_mul _
        _ < m := hdiff
    rw [hrw]
    intro hzero
    have hnorm_eq : ‖C g θ‖ = ‖(1 - (s : ℝ) : ℂ) * (C (fₙ n) θ - C g θ)‖ := by
      rw [← norm_neg ((1 - (s : ℝ) : ℂ) * (C (fₙ n) θ - C g θ))]
      congr 1
      linear_combination hzero
    rw [hnorm_eq] at hgθ
    exact absurd hgθ (not_le.mpr hpert_lt)
  have hG_loop : ∀ s ∈ Set.Icc (0 : ℝ) 1, G s 0 = G s τ := by
    intro s _
    simp only [hG_def]
    rw [hC_loop (fₙ n), hC_loop g]
  -- Input log at `s = 0` is the `fₙ` circle log; output at `s = 1` is the `g` circle.
  have hLfne' : ∀ θ ∈ Set.Icc (0 : ℝ) τ, Complex.exp (Lfn θ) = G 0 θ := by
    intro θ hθ
    rw [hLfne θ hθ]; simp only [hG_def]; push_cast; ring
  obtain ⟨Lg0, hLg0c, hLg0e, hLg0incr⟩ :=
    engine 0 1 G (by norm_num) hG_cont hG_ne hG_loop Lfn hLfnc hLfne' hLfnincr
  -- `G 1 θ = C g θ`, so `Lg0` is a log of the `g` circle on `[0, τ]`.
  have hLg0e_Cg : ∀ θ ∈ Set.Icc (0 : ℝ) τ, Complex.exp (Lg0 θ) = C g θ := by
    intro θ hθ
    rw [hLg0e θ hθ]; simp only [hG_def]; push_cast; ring
  -- Globalize the log of the `g` circle.
  obtain ⟨Lfinal, hLfinalc, hLfinale, hLfinalincr⟩ :=
    globalLog (C g) hCg_cont hCg_ne (fun θ => hC_per g θ) Lg0 hLg0c hLg0e_Cg hLg0incr
  refine ⟨Lfinal, hLfinalc, ?_, ?_⟩
  · intro θ
    rw [hLfinale θ]
  · rw [hτ_def] at hLfinalincr; exact hLfinalincr

/-- **Pointwise boundedness from compact equicontinuity and a fixed anchor value.** If a family
`F : ι → ℂ → ℂ` is equicontinuous on every compact set and all members agree at an anchor point
(`F i p = a` for all `i`), then at every point `z` the values `F i z` lie within a single radius of
`a`, uniformly in `i`. The radius is produced by chaining the uniform modulus of continuity along a
straight segment from `p` to `z`: subdivide `[p, z]` into `M` pieces shorter than the equicontinuity
gauge `δ` for oscillation `< 1`, so the telescoped oscillation of each `F i` over the segment is at
most `M`. -/
theorem pointwise_bounded_of_equicontinuousOn
    {ι : Type*} (F : ι → ℂ → ℂ) (p z a : ℂ) (hp : ∀ i, F i p = a)
    (heqc : ∀ K : Set ℂ, IsCompact K → EquicontinuousOn F K) :
    ∃ R : ℝ, ∀ i, dist (F i z) a ≤ R := by
  set S : Set ℂ := Metric.closedBall p (dist p z) with hS
  have hScpt : IsCompact S := isCompact_closedBall p (dist p z)
  have heq := heqc S hScpt
  rw [← equicontinuous_restrict_iff] at heq
  have : CompactSpace S := isCompact_iff_compactSpace.mp hScpt
  have hueq : UniformEquicontinuous (S.domRestrict ∘ F) :=
    CompactSpace.uniformEquicontinuous_of_equicontinuous heq
  rw [Metric.uniformEquicontinuous_iff] at hueq
  obtain ⟨δ, hδ0, hδ⟩ := hueq 1 one_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (dist p z / δ)
  set M : ℕ := N + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos N
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hMpos)
  set γ : ℕ → ℂ := fun k => p + ((k : ℂ) / (M : ℂ)) * (z - p) with hγ
  have hγ0 : γ 0 = p := by simp [hγ]
  have hγM : γ M = z := by simp only [hγ]; rw [div_self hMC]; ring
  have hcoef : ∀ k : ℕ, ‖((k : ℂ) / (M : ℂ))‖ = (k : ℝ) / M := by
    intro k; rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  have hγdist : ∀ k : ℕ, dist (γ k) p = ((k : ℝ) / M) * dist z p := by
    intro k
    simp only [hγ, dist_eq_norm]
    rw [show p + ((k : ℂ) / (M : ℂ)) * (z - p) - p = ((k : ℂ) / (M : ℂ)) * (z - p) from by ring,
      norm_mul, hcoef, ← dist_eq_norm]
  have hγS : ∀ k ≤ M, γ k ∈ S := by
    intro k hk
    rw [hS, Metric.mem_closedBall, hγdist, dist_comm z p]
    have hkM : (k : ℝ) / M ≤ 1 := by rw [div_le_one hMR]; exact_mod_cast hk
    nlinarith [dist_nonneg (x := p) (y := z), hkM]
  have hcons : ∀ k : ℕ, dist (γ k) (γ (k + 1)) = (1 / M) * dist z p := by
    intro k
    simp only [hγ, dist_eq_norm]
    have hcast : ((k + 1 : ℕ) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
    rw [hcast, show (p + ((k : ℂ) / (M : ℂ)) * (z - p)) - (p + (((k : ℂ) + 1) / (M : ℂ)) * (z - p))
          = (-(1 : ℂ) / (M : ℂ)) * (z - p) from by field_simp; ring, norm_mul]
    rw [show (-(1 : ℂ) / (M : ℂ)) = -(1 / (M : ℂ)) from by ring, norm_neg, norm_div,
      norm_one, Complex.norm_natCast, ← dist_eq_norm]
  have hconsδ : ∀ k : ℕ, dist (γ k) (γ (k + 1)) < δ := by
    intro k
    rw [hcons, dist_comm z p]
    have hlt : dist p z / M < δ := by
      rw [div_lt_iff₀ hMR]
      have h1 : dist p z / δ < M := by rw [hM]; push_cast; linarith
      rw [div_lt_iff₀ hδ0] at h1; linarith
    calc (1 / (M : ℝ)) * dist p z = dist p z / M := by ring
      _ < δ := hlt
  refine ⟨(M : ℝ), fun i => ?_⟩
  have hFstep : ∀ k < M, dist (F i (γ k)) (F i (γ (k + 1))) ≤ 1 := by
    intro k hk
    have hxS : γ k ∈ S := hγS k (le_of_lt hk)
    have hyS : γ (k + 1) ∈ S := hγS (k + 1) hk
    have hd := hδ ⟨γ k, hxS⟩ ⟨γ (k + 1), hyS⟩ (by rw [Subtype.dist_eq]; exact hconsδ k) i
    simp only [Function.comp_apply, Set.domRestrict_apply] at hd
    exact le_of_lt hd
  have hbound := dist_le_range_sum_of_dist_le (f := fun k => F i (γ k)) M
    (d := fun _ => (1 : ℝ)) (by intro k hk; exact hFstep k hk)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hbound
  rw [hγ0, hγM, hp i] at hbound
  rw [dist_comm]; exact hbound

/-- **Arzelà–Ascoli subsequence extraction in the compact-open topology.** A sequence of continuous
maps `Fₙ : ℕ → C(ℂ, ℂ)` that is equicontinuous on every compact subset of `ℂ` and pointwise
relatively compact (each orbit `{Fₙ z}` lies in a compact set) has a subsequence converging in the
compact-open (= locally uniform) topology of `C(ℂ, ℂ)`. The closure of the range is compact by the
Arzelà–Ascoli theorem (`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`, using that
`C(ℂ, ℂ)` embeds as a closed subspace of the space of uniform-on-compacta functions); since
`C(ℂ, ℂ)` is metrizable (`ℂ` is locally compact and σ-compact), compactness gives sequential
compactness and hence a convergent subsequence. -/
theorem exists_subseq_tendsto_continuousMap
    (Fn : ℕ → C(ℂ, ℂ))
    (heqc : ∀ K : Set ℂ, IsCompact K → EquicontinuousOn (fun n => (Fn n : ℂ → ℂ)) K)
    (hptcpt : ∀ z : ℂ, ∃ Q : Set ℂ, IsCompact Q ∧ ∀ n, Fn n z ∈ Q) :
    ∃ (φ : ℕ → ℕ) (g : C(ℂ, ℂ)), StrictMono φ ∧ Tendsto (Fn ∘ φ) atTop (𝓝 g) := by
  classical
  set 𝔖 : Set (Set ℂ) := {K | IsCompact K} with h𝔖
  have hce : IsClosedEmbedding
      (⇑(UniformOnFun.ofFun 𝔖) ∘ (DFunLike.coe : C(ℂ, ℂ) → (ℂ → ℂ))) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    rw [show (⇑(UniformOnFun.ofFun 𝔖) ∘ (DFunLike.coe : C(ℂ, ℂ) → (ℂ → ℂ)))
          = ContinuousMap.toUniformOnFunIsCompact from rfl,
        ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOfPred_continuous
      (CompactlyCoherentSpace.isCoherentWith (X := ℂ))
  set s : Set C(ℂ, ℂ) := Set.range Fn with hs
  have hKcpt : IsCompact (closure s) := by
    refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := 𝔖) (F := (DFunLike.coe : C(ℂ, ℂ) → (ℂ → ℂ)))
      (fun K hK => hK) hce ?_ ?_
    · intro K hK
      have hu : ∀ pt : s, ∃ n : ℕ, Fn n = (pt : C(ℂ, ℂ)) := by
        rintro ⟨_, n, rfl⟩; exact ⟨n, rfl⟩
      choose u hu using hu
      have heqfun : (fun n => (Fn n : ℂ → ℂ)) ∘ u
          = (DFunLike.coe : C(ℂ, ℂ) → (ℂ → ℂ)) ∘ (Subtype.val : s → C(ℂ, ℂ)) := by
        funext pt; simp only [Function.comp_apply, hu pt]
      have hcomp := (heqc K hK).comp u
      rwa [heqfun] at hcomp
    · intro K hK z hz
      obtain ⟨Q, hQ, hQmem⟩ := hptcpt z
      exact ⟨Q, hQ, by rintro i ⟨n, rfl⟩; exact hQmem n⟩
  have hmem : ∀ n, Fn n ∈ closure s := fun n => subset_closure ⟨n, rfl⟩
  obtain ⟨g, _hg, φ, hφ, htends⟩ := hKcpt.tendsto_subseq hmem
  exact ⟨φ, g, hφ, htends⟩

/-- **Homeomorphic limit from mutually inverse locally uniform limits.** If `fₖ → g` and `gₖ → h`
locally uniformly with each `gₖ` a two-sided inverse of `fₖ`, and `g`, `h` are continuous, then `g`
is a homeomorphism with inverse `h`. For each `z`, `fₖ z → g z`, so by continuity of `h` and local
uniform convergence of `gₖ`, `gₖ (fₖ z) → h (g z)`; but `gₖ (fₖ z) = z`, forcing `h (g z) = z`.
Symmetrically `g (h w) = w`. -/
theorem isHomeomorph_of_tendstoLocallyUniformly_inverse
    {fk gk : ℕ → ℂ → ℂ} {g h : ℂ → ℂ}
    (hg : Continuous g) (hh : Continuous h)
    (hfconv : TendstoLocallyUniformly (fun k a => fk k a) g atTop)
    (hgconv : TendstoLocallyUniformly (fun k a => gk k a) h atTop)
    (hli : ∀ k, Function.LeftInverse (gk k) (fk k))
    (hri : ∀ k, Function.RightInverse (gk k) (fk k)) :
    IsHomeomorph g := by
  rw [isHomeomorph_iff_exists_inverse]
  refine ⟨hg, h, ?_, ?_, hh⟩
  · intro z
    have hfz : Tendsto (fun k => fk k z) atTop (𝓝 (g z)) :=
      (tendstoLocallyUniformlyOn_univ.mpr hfconv).tendsto_at (mem_univ z)
    have hcomp : Tendsto (fun k => gk k (fk k z)) atTop (𝓝 (h (g z))) :=
      hgconv.tendsto_comp hh.continuousAt hfz
    have hconst : Tendsto (fun k => gk k (fk k z)) atTop (𝓝 z) := by
      simp only [hli _ z]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hcomp hconst
  · intro w
    have hgw : Tendsto (fun k => gk k w) atTop (𝓝 (h w)) :=
      (tendstoLocallyUniformlyOn_univ.mpr hgconv).tendsto_at (mem_univ w)
    have hcomp : Tendsto (fun k => fk k (gk k w)) atTop (𝓝 (g (h w))) :=
      hfconv.tendsto_comp hg.continuousAt hgw
    have hconst : Tendsto (fun k => fk k (gk k w)) atTop (𝓝 w) := by
      simp only [hri _ w]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hcomp hconst

/-- **Normal-family compactness of geometric quasiconformal maps.** A two-point–normalized,
uniformly `K`-quasiconformal sequence `fₙ : ℕ → ℂ → ℂ` has a subsequence converging locally
uniformly to a geometrically `K`-quasiconformal limit. The normalization fixes two distinct values:
`fₙ p = a` and `fₙ q = b` with `p ≠ q` and `a ≠ b`, for all `n`. This is the companion to the
closedness theorem `isQCGeometric_of_tendstoLocallyUniformly_inverse`
(`QC/Calculus/AnalyticClosedness.lean`): closedness shows the limit is `K`-quasiconformal *given*
locally uniform convergence of the maps and of their inverses to a homeomorphism pair, while
compactness produces the convergent subsequence, the convergent inverses, and the homeomorphic
limit.

The two-value normalization is exactly what makes the statement true on the plane `ℂ` (rather than
the sphere `ℂ̂`). The scale bound `dist (fₙ p) (fₙ q) = dist a b > 0` (from `a ≠ b`) — both an upper
and a lower bound — keeps the family from blowing up or degenerating, while the fixed anchor
`fₙ p = a` keeps it from escaping to infinity; without such a normalization the family `fₙ = n · id`
(uniformly `1`-quasiconformal) is not normal. The upper bound supplies the two-point datum of
`equicontinuousOn_of_uniform_isQCGeometric`, and the lower bound (`a ≠ b`, via
`exists_uniform_image_bound` for the inverse family) produces the image-side cover required by
`equicontinuousOn_inv_of_uniform_isQCGeometric`, giving equicontinuity of the family and of its
inverses on every compact set; with pointwise boundedness (anchored by `fₙ p = a` and `gₙ a = p`)
the Arzelà–Ascoli extraction `exists_subseq_tendsto_continuousMap` produces locally uniformly
convergent subsequences of both, whose limits are mutual inverses, so the limit is a homeomorphism
(`isHomeomorph_of_tendstoLocallyUniformly_inverse`) and hence `K`-quasiconformal by
closedness. -/
theorem exists_subseq_tendstoLocallyUniformly_isQCGeometric {fₙ : ℕ → ℂ → ℂ} {K : ℝ}
    {p q a b : ℂ} (hfK : ∀ n, IsQCGeometric (fₙ n) K) (hpq : p ≠ q) (hab : a ≠ b)
    (hfp : ∀ n, fₙ n p = a) (hfq : ∀ n, fₙ n q = b) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧ IsQCGeometric g K ∧
      TendstoLocallyUniformly (fun k => fₙ (φ k)) g atTop := by
  classical
  -- Continuity and the inverse homeomorphism of each member.
  have hcont : ∀ n, Continuous (fₙ n) := fun n => (hfK n).2.1.isHomeomorph.continuous
  set hom : ℕ → (ℂ ≃ₜ ℂ) := fun n => (hfK n).2.1.isHomeomorph.homeomorph (fₙ n) with hhom
  set gₙ : ℕ → ℂ → ℂ := fun n => (hom n).symm with hgₙ
  have hg_cont : ∀ n, Continuous (gₙ n) := fun n => (hom n).symm.continuous
  have hli : ∀ n, Function.LeftInverse (gₙ n) (fₙ n) := fun n => (hom n).left_inv
  have hri : ∀ n, Function.RightInverse (gₙ n) (fₙ n) := fun n => (hom n).right_inv
  -- The two-point normalization datum: the scale `dist (fₙ p) (fₙ q) = dist a b` is bounded above.
  set δ : ℝ := dist a b with hδ
  have hscale : ∀ n, dist (fₙ n p) (fₙ n q) = δ := by
    intro n; rw [hfp n, hfq n]
  have hub : ∀ n, dist (fₙ n p) (fₙ n q) ≤ δ := fun n => le_of_eq (hscale n)
  -- Forward equicontinuity on every compact set.
  have heqc_f : ∀ K' : Set ℂ, IsCompact K' → EquicontinuousOn fₙ K' := by
    intro K' hK'
    have hScpt : IsCompact (insert p (insert q K')) := (hK'.insert q).insert p
    have hpS : p ∈ insert p (insert q K') := Set.mem_insert _ _
    have hqS : q ∈ insert p (insert q K') := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    have hKsub : K' ⊆ insert p (insert q K') :=
      (Set.subset_insert _ _).trans (Set.subset_insert _ _)
    exact (equicontinuousOn_of_uniform_isQCGeometric hfK hScpt hpS hqS hpq hub).mono hKsub
  -- The inverse family is normalized at the image points `a, b`: `gₙ a = p`, `gₙ b = q`.
  have hga' : ∀ n, gₙ n a = p := by intro n; rw [← hfp n]; exact hli n p
  have hgb' : ∀ n, gₙ n b = q := by intro n; rw [← hfq n]; exact hli n q
  -- Inverse equicontinuity on every compact set. The image-side cover `U := closedBall p C` for the
  -- uniform inverse-image bound (`exists_uniform_image_bound` applied to the normalized inverse
  -- family) supplies the covering hypothesis of `equicontinuousOn_inv_of_uniform_isQCGeometric`.
  have hgKall : ∀ n, IsQCGeometric (gₙ n) K := by
    intro n
    have hinvK := isQCGeometric_inv_of_isQCGeometric (hfK n)
    have hbridge : ⇑((hfK n).2.1.isHomeomorph.homeomorph (fₙ n)).symm = gₙ n := by
      funext w
      have hfinj : Function.Injective (fₙ n) := (hfK n).2.1.isHomeomorph.injective
      have hL : fₙ n (((hfK n).2.1.isHomeomorph.homeomorph (fₙ n)).symm w) = w := by
        rw [← IsHomeomorph.homeomorph_apply (fₙ n) (hfK n).2.1.isHomeomorph
              (((hfK n).2.1.isHomeomorph.homeomorph (fₙ n)).symm w)]
        exact ((hfK n).2.1.isHomeomorph.homeomorph (fₙ n)).apply_symm_apply w
      have hR : fₙ n (gₙ n w) = w := hri n w
      exact hfinj (hL.trans hR.symm)
    rwa [hbridge] at hinvK
  have heqc_g : ∀ K' : Set ℂ, IsCompact K' → EquicontinuousOn gₙ K' := by
    intro K' hK'
    -- Uniform bound `C` on `dist (gₙ x₀)(gₙ x)` over the compact `insert a (insert b K')`.
    have hSacpt : IsCompact (insert a (insert b K')) := (hK'.insert b).insert a
    have haS : a ∈ insert a (insert b K') := Set.mem_insert _ _
    have hbS : b ∈ insert a (insert b K') := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    have hubg : ∀ n, dist (gₙ n a) (gₙ n b) ≤ dist p q := fun n => by
      rw [hga' n, hgb' n]
    obtain ⟨C, hC⟩ := exists_uniform_image_bound hgKall hSacpt haS hbS hab hubg
    -- `U := closedBall p C` covers all `gₙ '' K'`, so `K' ⊆ fₙ '' U`.
    set U : Set ℂ := Metric.closedBall p C with hUdef
    have hUcpt : IsCompact U := isCompact_closedBall p C
    have hTU : ∀ n, K' ⊆ fₙ n '' U := by
      intro n z hz
      refine ⟨gₙ n z, ?_, hri n z⟩
      rw [hUdef, Metric.mem_closedBall, ← hga' n]
      exact hC n z (Set.subset_insert _ _ (Set.subset_insert _ _ hz)) a haS
    exact equicontinuousOn_inv_of_uniform_isQCGeometric hfK gₙ (fun n => ⟨hli n, hri n⟩) hK' hUcpt
      hTU
  -- Pointwise boundedness of both families.
  have hga : ∀ n, gₙ n a = p := by intro n; rw [← hfp n]; exact hli n p
  have hbd_f : ∀ z : ℂ, ∃ Q : Set ℂ, IsCompact Q ∧ ∀ n, fₙ n z ∈ Q := by
    intro z
    obtain ⟨R, hR⟩ := pointwise_bounded_of_equicontinuousOn fₙ p z a hfp heqc_f
    exact ⟨Metric.closedBall a R, isCompact_closedBall a R, fun n => by
      rw [Metric.mem_closedBall]; exact hR n⟩
  have hbd_g : ∀ z : ℂ, ∃ Q : Set ℂ, IsCompact Q ∧ ∀ n, gₙ n z ∈ Q := by
    intro z
    obtain ⟨R, hR⟩ := pointwise_bounded_of_equicontinuousOn gₙ a z p hga heqc_g
    exact ⟨Metric.closedBall p R, isCompact_closedBall p R, fun n => by
      rw [Metric.mem_closedBall]; exact hR n⟩
  -- Bundle as continuous maps.
  set Fn : ℕ → C(ℂ, ℂ) := fun n => ⟨fₙ n, hcont n⟩ with hFn
  set Gn : ℕ → C(ℂ, ℂ) := fun n => ⟨gₙ n, hg_cont n⟩ with hGn
  -- First extraction: a subsequence of the forward family converging in `C(ℂ, ℂ)`.
  obtain ⟨φ₁, g₀, hφ₁, htends_f⟩ :=
    exists_subseq_tendsto_continuousMap Fn heqc_f hbd_f
  -- Second extraction: a further subsequence making the inverse family converge.
  have heqc_g' : ∀ K' : Set ℂ, IsCompact K' →
      EquicontinuousOn (fun k => ((Gn ∘ φ₁) k : ℂ → ℂ)) K' := by
    intro K' hK'
    exact (heqc_g K' hK').comp φ₁
  have hbd_g' : ∀ z : ℂ, ∃ Q : Set ℂ, IsCompact Q ∧ ∀ k, (Gn ∘ φ₁) k z ∈ Q := by
    intro z
    obtain ⟨Q, hQ, hQmem⟩ := hbd_g z
    exact ⟨Q, hQ, fun k => hQmem (φ₁ k)⟩
  obtain ⟨φ₂, h₀, hφ₂, htends_g⟩ :=
    exists_subseq_tendsto_continuousMap (Gn ∘ φ₁) heqc_g' hbd_g'
  -- The combined subsequence index.
  set φ : ℕ → ℕ := φ₁ ∘ φ₂ with hφ_def
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  -- Forward convergence persists along the sub-subsequence.
  have htends_f' : Tendsto (Fn ∘ φ) atTop (𝓝 g₀) := by
    have := htends_f.comp hφ₂.tendsto_atTop
    simpa [Function.comp_assoc, hφ_def] using this
  have htends_g' : Tendsto (Gn ∘ φ) atTop (𝓝 h₀) := by
    simpa [Function.comp_assoc, hφ_def] using htends_g
  -- Convert both to locally uniform convergence.
  have hlu_f : TendstoLocallyUniformly (fun k a => (Fn (φ k) : ℂ → ℂ) a) (g₀ : ℂ → ℂ) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp htends_f'
  have hlu_g : TendstoLocallyUniformly (fun k a => (Gn (φ k) : ℂ → ℂ) a) (h₀ : ℂ → ℂ) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp htends_g'
  -- The limit `g₀` is a homeomorphism with inverse `h₀`.
  have hg₀_homeo : IsHomeomorph (g₀ : ℂ → ℂ) :=
    isHomeomorph_of_tendstoLocallyUniformly_inverse g₀.continuous h₀.continuous
      hlu_f hlu_g (fun k => hli (φ k)) (fun k => hri (φ k))
  -- Closedness (analytic route): the limit is geometrically `K`-quasiconformal.
  have hQC : IsQCGeometric (g₀ : ℂ → ℂ) K :=
    isQCGeometric_of_tendstoLocallyUniformly_inverse (fun k => hfK (φ k))
      (fun k => hgKall (φ k)) (fun k => hli (φ k)) (fun k => hri (φ k))
      hlu_f hlu_g hg₀_homeo
  exact ⟨φ, (g₀ : ℂ → ℂ), hφ, hQC, hlu_f⟩

end NoWanderingDomains
