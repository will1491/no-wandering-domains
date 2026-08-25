/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.LengthArea.CurveModulus

/-!
# Length–area: weak-derivative bridge, energy finiteness, and mollification

Continues `LengthArea.CurveModulus`. The a.e. agreement of the classical directional
derivative with the weak directional derivative (`fderiv_ae_eq_weakDirDeriv`), finiteness of
the squared-`fderiv` ball energy (`IsQCAnalytic.lintegralSq_fderiv_ball_ne_top`), the
`curveModulus`-nullity of curves with infinite line integral, and the `ContDiffBump`-mollifier
approximation of the differential (convolution energy and `fderiv` limits) feeding the Fuglede
upper-gradient argument.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace NoWanderingDomains

set_option maxHeartbeats 400000 in
-- The proof inlines a horizontal core (Fubini transfer to `ℝ × ℝ`, per-line FTC and
-- difference-quotient uniqueness) and the `v = I` reduction through the coordinate
-- swap `σ`, so the elaboration is long and the heartbeat budget is raised.
/-- **Strong ⇄ weak directional derivative, a.e. bridge (`v ∈ {1, I}`).** For an
almost-everywhere-differentiable, locally integrable function `f` with a locally
integrable weak directional derivative `g` in the real direction `v ∈ {1, I}`, the
*classical* directional derivative `z ↦ (fderiv ℝ f z) v` agrees with `g` almost
everywhere.

Proof (converse-ACL route): apply the project's converse-of-ACL representative
theorem (`exists_aclHorizontal_of_hasWeakDirDeriv_one` for `v = 1`,
`exists_aclVertical_of_hasWeakDirDeriv_I` for `v = I`) to obtain a representative
`f' =ᵐ f` that is absolutely continuous on almost every line with line-derivative
`g`. Working in `ℝ × ℝ` coordinates, on almost every line the AC representative
satisfies, by the fundamental theorem of calculus, `f'(x+s) − f'(x) = ∫ₓ^{x+s} g`,
whose difference quotient tends to `g(x)` for a.e. `x` by the Lebesgue
differentiation theorem. Since `f' =ᵐ f`, the difference quotient of `f` agrees
with that of `f'` for a.e. shift `s` (Fubini), so it has the same limit `g(x)`.
But `f` is differentiable at `(x, y)`, so its difference quotient along the line
has the *full* limit `(fderiv ℝ f (x,y)) v`; uniqueness of limits forces
`(fderiv ℝ f (x,y)) v = g (x,y)`. -/
theorem fderiv_ae_eq_weakDirDeriv {f g : ℂ → ℂ} {v : ℂ}
    (hg : HasWeakDirDeriv v g f Set.univ) (hgloc : LocallyIntegrableOn g Set.univ)
    (hdiff : ∀ᵐ z, DifferentiableAt ℝ f z)
    (hv : v = 1 ∨ v = Complex.I) (hfloc : LocallyIntegrable f) :
    ∀ᵐ z, (fderiv ℝ f z) v = g z := by
  classical
  rw [locallyIntegrableOn_univ] at hgloc
  -- ============================================================
  -- A one-dimensional uniqueness fact: an a.e.-zero function with a derivative at a
  -- point where it vanishes has derivative `0` there. The difference quotient is
  -- identically `0` along the co-null (hence dense, punctured) set where the
  -- function vanishes, so the limit is `0`.
  -- ============================================================
  have aux : ∀ {D : ℝ → ℂ} {x : ℝ} {c : ℂ},
      D =ᵐ[volume] 0 → D x = 0 → HasDerivAt D c x → c = 0 := by
    intro D x c hD0 hDx hderiv
    -- The co-null set where `D` vanishes is dense; deleting `x` keeps it dense.
    have hSdense : Dense {b : ℝ | D b = 0} :=
      MeasureTheory.Measure.dense_of_ae (by filter_upwards [hD0] with b hb using hb)
    have hSx : Dense ({b : ℝ | D b = 0} \ {x}) := hSdense.sdiff_singleton x
    have hxmem : x ∈ closure ({b : ℝ | D b = 0} \ {x}) := hSx.closure_eq ▸ Set.mem_univ x
    have hNeBot : (nhdsWithin x ({b : ℝ | D b = 0} \ {x})).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hxmem
    -- The slope tends to `c` along `𝓝[≠]x`, hence along the finer dense punctured filter.
    have htend : Filter.Tendsto (slope D x) (nhdsWithin x {x}ᶜ) (nhds c) :=
      hasDerivAt_iff_tendsto_slope.mp hderiv
    have hsub : ({b : ℝ | D b = 0} \ {x}) ⊆ ({x}ᶜ : Set ℝ) := fun b hb => by
      simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hb
      simp [Set.mem_compl_iff, Set.mem_singleton_iff, hb.2]
    have htend' : Filter.Tendsto (slope D x)
        (nhdsWithin x ({b : ℝ | D b = 0} \ {x})) (nhds c) :=
      htend.mono_left (nhdsWithin_mono x hsub)
    -- On that set the slope is identically `0`.
    have hslope0 : Filter.Tendsto (slope D x)
        (nhdsWithin x ({b : ℝ | D b = 0} \ {x})) (nhds (0 : ℂ)) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with b hb
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hb
      rw [slope_def_module, hb.1, hDx, sub_zero, smul_zero]
    exact tendsto_nhds_unique htend' hslope0
  -- ============================================================
  -- THE HORIZONTAL CORE: the statement for the direction `1`.
  -- ============================================================
  have core : ∀ {f g : ℂ → ℂ}, HasWeakDirDeriv 1 g f Set.univ → LocallyIntegrable g →
      (∀ᵐ z, DifferentiableAt ℝ f z) → LocallyIntegrable f →
      ∀ᵐ z, (fderiv ℝ f z) 1 = g z := by
    clear hg hgloc hdiff hv hfloc f g v
    intro f g hg hgL hdiff hfL
    -- The AC representative `f'` of `f` with horizontal line-derivative `g`.
    obtain ⟨f', hf'ae, hacl⟩ := exists_aclHorizontal_of_hasWeakDirDeriv_one hfL hgL hg
    -- Move to `ℝ × ℝ` through the volume-preserving real-coordinate equivalence.
    have hemb := Complex.measurableEquivRealProd.measurableEmbedding
    have hmp := Complex.volume_preserving_equiv_real_prod
    have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
        (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
      hmp.symm Complex.measurableEquivRealProd
    -- `f' =ᵐ f` on `ℂ`, transferred to `ℝ × ℝ` slices.
    have hf'ae2 : (fun p : ℝ × ℝ => f' ⟨p.1, p.2⟩) =ᵐ[volume.prod volume]
        (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩) := by
      rw [← Measure.volume_eq_prod]
      have := hmpsymm.quasiMeasurePreserving.ae_eq_comp hf'ae
      filter_upwards [this] with p hp
      simpa [Complex.measurableEquivRealProd_symm_apply] using hp
    -- `f` differentiable a.e., transferred to `ℝ × ℝ`.
    have hdiff2 : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ f ⟨p.1, p.2⟩ := by
      have := hmpsymm.quasiMeasurePreserving.ae hdiff
      filter_upwards [this] with p hp
      simpa [Complex.measurableEquivRealProd_symm_apply] using hp
    -- Per-line a.e.-equality of the slices, from `hf'ae2` by Fubini.
    have hslice_eq : ∀ᵐ y : ℝ,
        (fun x : ℝ => f' ⟨x, y⟩) =ᵐ[volume] (fun x : ℝ => f ⟨x, y⟩) := by
      have hswap : (fun p : ℝ × ℝ => f' ⟨p.2, p.1⟩) =ᵐ[volume.prod volume]
          (fun p : ℝ × ℝ => f ⟨p.2, p.1⟩) := by
        have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae_eq hf'ae2
        simpa [Function.comp_def, Prod.swap] using h
      exact Measure.ae_ae_eq_of_ae_eq_uncurry hswap
    -- Per-line a.e.-`DifferentiableAt`, from `hdiff2` by Fubini.
    have hdiff_line : ∀ᵐ y : ℝ,
        ∀ᵐ x : ℝ, DifferentiableAt ℝ f ⟨x, y⟩ := by
      have hswap : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ f ⟨p.2, p.1⟩ := by
        have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae hdiff2
        simpa [Prod.swap] using! h
      exact MeasureTheory.Measure.ae_ae_of_ae_prod hswap
    -- The conclusion, assembled at the `ℝ × ℝ` level via the curried per-line facts.
    -- We first prove the per-line statement `∀ᵐ y, ∀ᵐ x, GOAL⟨x,y⟩`, then transfer
    -- back to `ℂ` through the measure-preserving equivalence.
    have hline : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, (fderiv ℝ f ⟨x, y⟩) 1 = g ⟨x, y⟩ := by
      filter_upwards [hacl, hslice_eq, hdiff_line] with y hy_acl hy_eq hy_diff
      obtain ⟨_, hy_deriv⟩ := hy_acl
      -- On this good line, the f'-slice has `HasDerivAt … (g⟨x,y⟩)` a.e.,
      -- `f` is differentiable, and the two slices agree a.e.
      filter_upwards [hy_deriv, hy_diff, hy_eq] with x hx_deriv hx_diff hx_eq
      -- (i) the `f`-slice has `HasDerivAt … ((fderiv ℝ f ⟨x,y⟩) 1)` (line direction 1).
      have hsliceF : HasDerivAt (fun t : ℝ => f ⟨t, y⟩) ((fderiv ℝ f ⟨x, y⟩) 1) x := by
        have haff : HasDerivAt (fun t : ℝ => (⟨t, y⟩ : ℂ)) (1 : ℂ) x := by
          have he : (fun t : ℝ => (⟨t, y⟩ : ℂ)) =
              fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
            funext t; apply Complex.ext <;> simp
          rw [he]
          simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I)
        have hfd : HasFDerivAt f (fderiv ℝ f ⟨x, y⟩) ⟨x, y⟩ := hx_diff.hasFDerivAt
        simpa using! hfd.comp_hasDerivAt x haff
      -- (ii) the `f'`-slice has `HasDerivAt … (g⟨x,y⟩)`.
      -- (iii) the slices agree a.e. (in the line variable) and at `x`.
      -- The difference `D` is a.e. zero, vanishes at `x`, and has derivative
      -- `(fderiv ℝ f ⟨x,y⟩) 1 - g⟨x,y⟩`; by `aux` that derivative is `0`.
      have hDae : (fun t : ℝ => f ⟨t, y⟩ - f' ⟨t, y⟩) =ᵐ[volume] 0 := by
        filter_upwards [hy_eq] with t ht
        simp only [Pi.zero_apply]
        rw [ht]; ring
      have hDx : (fun t : ℝ => f ⟨t, y⟩ - f' ⟨t, y⟩) x = 0 := by
        change f ⟨x, y⟩ - f' ⟨x, y⟩ = 0; rw [hx_eq]; ring
      have hDderiv : HasDerivAt (fun t : ℝ => f ⟨t, y⟩ - f' ⟨t, y⟩)
          ((fderiv ℝ f ⟨x, y⟩) 1 - g ⟨x, y⟩) x := hsliceF.sub hx_deriv
      exact sub_eq_zero.mp (aux hDae hDx hDderiv)
    -- Transfer `∀ᵐ y, ∀ᵐ x, P⟨x,y⟩` back to `∀ᵐ z:ℂ, P z`.
    -- The predicate set is measurable once `g` is replaced by a strongly-measurable
    -- representative `g₀ =ᵐ g`; we prove the conclusion for `g₀` at the `ℝ × ℝ` level
    -- via `ae_prod_iff_ae_ae`, pull it back along the equivalence, then return to `g`.
    set g₀ : ℂ → ℂ := hgL.aestronglyMeasurable.mk g with hg₀_def
    have hg₀_ae : g =ᵐ[volume] g₀ := hgL.aestronglyMeasurable.ae_eq_mk
    have hg₀_meas : Measurable g₀ := hgL.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    -- The lifted predicate, with `g₀`, has a measurable set.
    have hLHSmeas : Measurable (fun p : ℝ × ℝ => (fderiv ℝ f ⟨p.1, p.2⟩) 1) :=
      (measurable_fderiv_apply_const ℝ f 1).comp Complex.measurableEquivRealProd.symm.measurable
    have hRHSmeas : Measurable (fun p : ℝ × ℝ => g₀ ⟨p.1, p.2⟩) :=
      hg₀_meas.comp Complex.measurableEquivRealProd.symm.measurable
    have hmeasSet : MeasurableSet
        {p : ℝ × ℝ | (fderiv ℝ f ⟨p.1, p.2⟩) 1 = g₀ ⟨p.1, p.2⟩} :=
      measurableSet_eq_fun hLHSmeas hRHSmeas
    -- The per-line statement upgraded from `g` to `g₀` (they agree a.e. per line).
    have hg₀_line : ∀ᵐ y : ℝ,
        (fun x : ℝ => g ⟨x, y⟩) =ᵐ[volume] (fun x : ℝ => g₀ ⟨x, y⟩) := by
      have hg₀2 : (fun p : ℝ × ℝ => g ⟨p.2, p.1⟩) =ᵐ[volume.prod volume]
          (fun p : ℝ × ℝ => g₀ ⟨p.2, p.1⟩) := by
        have hg₀prod : (fun p : ℝ × ℝ => g ⟨p.1, p.2⟩) =ᵐ[volume.prod volume]
            (fun p : ℝ × ℝ => g₀ ⟨p.1, p.2⟩) := by
          rw [← Measure.volume_eq_prod]
          have := hmpsymm.quasiMeasurePreserving.ae_eq_comp hg₀_ae
          filter_upwards [this] with p hp
          simpa [Complex.measurableEquivRealProd_symm_apply] using hp
        have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae_eq hg₀prod
        simpa [Function.comp_def, Prod.swap] using h
      exact Measure.ae_ae_eq_of_ae_eq_uncurry hg₀2
    have hline₀ : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, (fderiv ℝ f ⟨x, y⟩) 1 = g₀ ⟨x, y⟩ := by
      filter_upwards [hline, hg₀_line] with y hy hy₀
      filter_upwards [hy, hy₀] with x hx hx₀
      rw [hx, hx₀]
    have hprod : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
        (fderiv ℝ f ⟨p.1, p.2⟩) 1 = g₀ ⟨p.1, p.2⟩ := by
      rw [Measure.ae_prod_iff_ae_ae hmeasSet,
        Measure.ae_ae_comm (p := fun a b : ℝ => (fderiv ℝ f ⟨a, b⟩) 1 = g₀ ⟨a, b⟩) hmeasSet]
      exact hline₀
    have hprod' : ∀ᵐ p : ℝ × ℝ, (fderiv ℝ f ⟨p.1, p.2⟩) 1 = g₀ ⟨p.1, p.2⟩ := by
      rwa [← Measure.volume_eq_prod] at hprod
    have hcz₀ : ∀ᵐ z : ℂ, (fderiv ℝ f z) 1 = g₀ z := by
      have := hmp.quasiMeasurePreserving.ae hprod'
      filter_upwards [this] with z hz
      simpa [Complex.measurableEquivRealProd_apply] using hz
    filter_upwards [hcz₀, hg₀_ae] with z hz hz₀
    rw [hz, ← hz₀]
  -- ============================================================
  -- DISPATCH on the direction.
  -- ============================================================
  rcases hv with rfl | rfl
  · exact core hg hgloc hdiff hfloc
  · -- Reduce `v = I` to `v = 1` via the real/imaginary coordinate swap
    -- `σ z = I · conj z`, exactly as in `exists_aclVertical_of_hasWeakDirDeriv_I`.
    -- The rotation parameter is introduced as a genuine element of `Circle` (with its value
    -- recorded in `hcI`) so that `rotation_apply` matches at strict transparency.
    obtain ⟨cI, hcI⟩ : ∃ c : Circle, (c : ℂ) = Complex.I :=
      ⟨⟨Complex.I, by simp [Submonoid.unitSphere, Metric.sphere]⟩, rfl⟩
    set σ : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.conjLIE.trans (rotation cI) with hσ_def
    have hσ_apply : ∀ z : ℂ, σ z = ⟨z.im, z.re⟩ := by
      intro z
      simp only [hσ_def, LinearIsometryEquiv.trans_apply, Complex.conjLIE_apply, rotation_apply,
        hcI]
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    have hσ_invol : ∀ z : ℂ, σ (σ z) = z := by
      intro z; rw [hσ_apply, hσ_apply]
    -- `σ · I = 1` (the only direction needed below): `σ⟨0,1⟩ = ⟨1,0⟩ = 1`.
    have hσ_I : (σ : ℂ →L[ℝ] ℂ) Complex.I = 1 := by
      have : σ Complex.I = 1 := by rw [hσ_apply]; apply Complex.ext <;> simp
      simpa using this
    -- `σ · 1 = I` (used to read off the conclusion at the end).
    have hσ_one : (σ : ℂ →L[ℝ] ℂ) (1 : ℂ) = Complex.I := by
      have : σ (1 : ℂ) = Complex.I := by rw [hσ_apply]; apply Complex.ext <;> simp
      simpa using this
    have hmp : MeasurePreserving σ volume volume := σ.measurePreserving
    have hemb : MeasurableEmbedding σ := σ.toMeasurableEquiv.measurableEmbedding
    -- Transfer the weak directional derivative to the direction `1`.
    have hweak : HasWeakDirDeriv 1 (fun z => g (σ z)) (fun z => f (σ z)) Set.univ := by
      intro ψ hψ_smooth hψ_cpt _
      have hchain : ∀ w : ℂ,
          (fderiv ℝ (fun z => ψ (σ z)) w) Complex.I = (fderiv ℝ ψ (σ w)) 1 := by
        intro w
        have hd1 : DifferentiableAt ℝ ψ (σ w) :=
          (hψ_smooth.differentiable (by norm_num)).differentiableAt
        have hσd : DifferentiableAt ℝ (fun z => σ z) w :=
          σ.toContinuousLinearEquiv.differentiableAt
        have he : (fun z => ψ (σ z)) = ψ ∘ (fun z => σ z) := rfl
        rw [he, fderiv_comp w hd1 hσd]
        have hσfd : fderiv ℝ (fun z => σ z) w = (σ : ℂ →L[ℝ] ℂ) :=
          (σ.toContinuousLinearEquiv.hasFDerivAt).fderiv
        rw [hσfd]
        simp only [ContinuousLinearMap.comp_apply]
        rw [hσ_I]
      have hψσ_smooth := hψ_smooth.comp σ.toContinuousLinearEquiv.contDiff
      have hψσ_cpt : HasCompactSupport (fun z => ψ (σ z)) := by
        have := hψ_cpt.comp_homeomorph σ.toHomeomorph
        simpa using! this
      have hH := hg (fun z => ψ (σ z)) hψσ_smooth hψσ_cpt (by simp)
      rw [show (fun z => ((fderiv ℝ (fun z => ψ (σ z)) z) Complex.I) • f z)
            = (fun z => ((fderiv ℝ ψ (σ z)) 1) • f z) from
            funext (fun z => by rw [hchain z])] at hH
      have hLHS : (∫ w, ((fderiv ℝ ψ w) 1) • f (σ w))
          = ∫ z, ((fderiv ℝ ψ (σ z)) 1) • f z := by
        have := MeasureTheory.integral_comp σ (fun w => ((fderiv ℝ ψ w) 1) • f (σ w))
        rw [← this]
        refine integral_congr_ae ?_; filter_upwards with z; rw [hσ_invol]
      have hRHS : (∫ w, ψ w • g (σ w)) = ∫ z, ψ (σ z) • g z := by
        have := MeasureTheory.integral_comp σ (fun w => ψ w • g (σ w))
        rw [← this]
        refine integral_congr_ae ?_; filter_upwards with z; rw [hσ_invol]
      rw [hLHS, hRHS]
      exact hH
    -- Local integrability of `f∘σ` and `g∘σ`, preserved by `σ`.
    have hLIcomp : ∀ {u : ℂ → ℂ}, LocallyIntegrable u volume →
        LocallyIntegrable (fun z => u (σ z)) volume := by
      intro u hu
      rw [MeasureTheory.locallyIntegrable_iff]
      intro K hK
      have hpre : (σ ⁻¹' (σ '' K)) = K := Set.preimage_image_eq _ σ.injective
      have hKimg : IsCompact (σ '' K) := hK.image σ.continuous
      have := (hmp.integrableOn_comp_preimage hemb (f := u) (s := σ '' K)).mpr
        (hu.integrableOn_isCompact hKimg)
      rwa [hpre] at this
    -- `f∘σ` differentiable a.e. (`σ` is a diffeo and measure-preserving).
    have hdiffσ : ∀ᵐ w, DifferentiableAt ℝ (fun z => f (σ z)) w := by
      have hpre := hmp.quasiMeasurePreserving.ae hdiff
      filter_upwards [hpre] with w hw
      exact hw.comp w σ.toContinuousLinearEquiv.differentiableAt
    -- Apply the horizontal core to `F := f∘σ`, `G := g∘σ`.
    have hcore := core hweak (hLIcomp hgloc) hdiffσ (hLIcomp hfloc)
    -- `(fderiv ℝ (f∘σ) w) 1 = (fderiv ℝ f (σ w)) (σ 1) = (fderiv ℝ f (σ w)) I`.
    have hkey : ∀ᵐ w, (fderiv ℝ f (σ w)) Complex.I = g (σ w) := by
      filter_upwards [hcore, hmp.quasiMeasurePreserving.ae hdiff] with w hw hwd
      have hσd : DifferentiableAt ℝ (fun z => σ z) w :=
        σ.toContinuousLinearEquiv.differentiableAt
      have hchainw : (fderiv ℝ (fun z => f (σ z)) w) (1 : ℂ)
          = (fderiv ℝ f (σ w)) Complex.I := by
        have he : (fun z => f (σ z)) = f ∘ (fun z => σ z) := rfl
        rw [he, fderiv_comp w hwd hσd]
        have hσfd : fderiv ℝ (fun z => σ z) w = (σ : ℂ →L[ℝ] ℂ) :=
          (σ.toContinuousLinearEquiv.hasFDerivAt).fderiv
        rw [hσfd]
        simp only [ContinuousLinearMap.comp_apply]
        rw [hσ_one]
      rw [← hchainw]; exact hw
    -- Change variables `w ↦ σ w` (measure-preserving involution) to conclude.
    have := hmp.quasiMeasurePreserving.ae hkey
    filter_upwards [this] with z hz
    rw [hσ_invol] at hz
    exact hz

/-- **`G := ‖Df‖` is square-integrable on every ball (de-gated form).** For a continuous,
almost-everywhere differentiable `f ∈ W^{1,2}_loc`, the operator norm
`G z := ‖fderiv ℝ f z‖₊` of the (strong) differential has finite `L²`-energy on every
Euclidean ball: `∫⁻_{ball 0 R} G² < ∞`.

This is the genuine Sobolev input, stated over the explicit hypothesis triple
(continuity + a.e. differentiability + `MemW12loc`) rather than `IsQCAnalytic`, so it applies
to any Sobolev homeomorphism-like map — in particular to the inverse of a geometric
quasiconformal map, whose a.e. differentiability is obtained without any Beltrami equation.
It combines (a) the a.e. identification of the strong differential `fderiv ℝ f` with the weak
gradient `(gx, gy)` of `MemW12loc f` (where `f` is differentiable a.e., the columns of
`fderiv ℝ f` are the weak partials — the converse-of-ACL bridge `fderiv_ae_eq_weakDirDeriv`),
giving the pointwise a.e. bound `‖fderiv ℝ f z‖ ≤ ‖gx z‖ + ‖gy z‖`, with (b) the
`L²_loc` membership of `gx, gy` from `MemW12loc f`, which makes `‖gx‖ + ‖gy‖`
square-integrable on the compact closed ball `closedBall 0 R ⊇ ball 0 R`. The
strong⇄weak a.e. bridge is `fderiv_ae_eq_weakDirDeriv`. -/
theorem lintegralSq_fderiv_ball_ne_top_of_memW12loc {f : ℂ → ℂ}
    (hfcont : Continuous f) (hdiff : ∀ᵐ z, DifferentiableAt ℝ f z) (hW12 : MemW12loc f)
    (R : ℝ) :
    (∫⁻ z in Metric.ball (0 : ℂ) R, (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := by
  classical
  -- Extract the weak gradient `(gx, gy)` from `MemW12loc f`.
  obtain ⟨_hLp, gx, gy, ⟨hwgx, hwgy⟩, hmgx, hmgy⟩ := hW12
  -- `hmgx : MemWklocP gx 0 2 univ = MemLpLocOn gx 2 univ`; likewise `hmgy`.
  have hLpgx : MemLpLocOn gx 2 Set.univ := hmgx
  have hLpgy : MemLpLocOn gy 2 Set.univ := hmgy
  -- The compact closed ball `K := closedBall 0 R ⊇ ball 0 R`.
  set K : Set ℂ := Metric.closedBall (0 : ℂ) R with hK
  have hKcompact : IsCompact K := isCompact_closedBall (0 : ℂ) R
  -- `L²_loc` membership of `gx, gy` on the compact `K` ⟹ they are integrable on `K`,
  -- hence locally integrable on `univ` (used for the uniqueness bridge below).
  have hgxK : MemLp gx 2 (volume.restrict K) := hLpgx K (Set.subset_univ _) hKcompact
  have hgyK : MemLp gy 2 (volume.restrict K) := hLpgy K (Set.subset_univ _) hKcompact
  -- `MemLpLocOn _ 2` ⟹ integrable on every compact set ⟹ locally integrable.
  have memLpLoc_to_loc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      LocallyIntegrableOn g Set.univ := by
    intro g hg
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    have : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    have hmem1 : MemLp g 1 (volume.restrict k) :=
      (hg k (Set.subset_univ _) hk).mono_exponent (by norm_num)
    exact memLp_one_iff_integrable.mp hmem1
  have hgxloc : LocallyIntegrableOn gx Set.univ := memLpLoc_to_loc hLpgx
  have hgyloc : LocallyIntegrableOn gy Set.univ := memLpLoc_to_loc hLpgy
  -- `f` is locally integrable: it is continuous.
  have hfloc : LocallyIntegrable f := hfcont.locallyIntegrable
  -- The strong⇄weak a.e. bridge: classical partials equal the weak partials a.e.
  have haex : ∀ᵐ z, (fderiv ℝ f z) (1 : ℂ) = gx z :=
    fderiv_ae_eq_weakDirDeriv hwgx hgxloc hdiff (Or.inl rfl) hfloc
  have haey : ∀ᵐ z, (fderiv ℝ f z) Complex.I = gy z :=
    fderiv_ae_eq_weakDirDeriv hwgy hgyloc hdiff (Or.inr rfl) hfloc
  -- Pointwise a.e. bound: `‖fderiv ℝ f z‖ ≤ ‖gx z‖ + ‖gy z‖`.
  have hbound : ∀ᵐ z, (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ≤ (‖gx z‖₊ : ℝ≥0∞) + (‖gy z‖₊ : ℝ≥0∞) := by
    filter_upwards [haex, haey] with z hzx hzy
    -- `‖T‖ ≤ ‖T 1‖ + ‖T I‖` via the basis decomposition `w = w.re • 1 + w.im • I`.
    have hopn : ‖fderiv ℝ f z‖ ≤ ‖(fderiv ℝ f z) (1 : ℂ)‖ + ‖(fderiv ℝ f z) Complex.I‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
      set T := fderiv ℝ f z with hT
      -- `T w = w.re • T 1 + w.im • T I` from `w = w.re • 1 + w.im • I` and linearity.
      have hTw : T w = w.re • T (1 : ℂ) + w.im • T Complex.I := by
        have hdecomp : w = w.re • (1 : ℂ) + w.im • Complex.I := by
          rw [Complex.real_smul, Complex.real_smul, mul_one]
          exact (Complex.re_add_im w).symm
        conv_lhs => rw [hdecomp]
        simp only [map_add, map_smul]
      calc ‖T w‖ = ‖w.re • T (1 : ℂ) + w.im • T Complex.I‖ := by rw [hTw]
        _ ≤ ‖w.re • T (1 : ℂ)‖ + ‖w.im • T Complex.I‖ := norm_add_le _ _
        _ ≤ ‖(w.re : ℝ)‖ * ‖T (1 : ℂ)‖ + ‖(w.im : ℝ)‖ * ‖T Complex.I‖ := by
            gcongr <;> exact norm_smul_le _ _
        _ = |w.re| * ‖T (1 : ℂ)‖ + |w.im| * ‖T Complex.I‖ := by
            rw [Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ ‖w‖ * ‖T (1 : ℂ)‖ + ‖w‖ * ‖T Complex.I‖ := by
            gcongr <;> [exact Complex.abs_re_le_norm w; exact Complex.abs_im_le_norm w]
        _ = (‖T (1 : ℂ)‖ + ‖T Complex.I‖) * ‖w‖ := by ring
    rw [hzx, hzy] at hopn
    -- Transfer the real bound to `ℝ≥0∞`.
    have hnn : ‖fderiv ℝ f z‖₊ ≤ ‖gx z‖₊ + ‖gy z‖₊ := by
      rw [← NNReal.coe_le_coe]; push_cast; exact hopn
    calc (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ≤ ((‖gx z‖₊ + ‖gy z‖₊ : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.mpr hnn
      _ = (‖gx z‖₊ : ℝ≥0∞) + (‖gy z‖₊ : ℝ≥0∞) := by push_cast; ring
  -- The `L²`-energy of each weak partial on the compact `K` is finite.
  have hsqfin : ∀ {g : ℂ → ℂ}, MemLp g 2 (volume.restrict K) →
      (∫⁻ z in K, (‖g z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := by
    intro g hg
    have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := volume.restrict K)
      (f := g) (p := 2) (by norm_num) (by norm_num) hg.eLpNorm_lt_top
    -- `∫⁻ ‖g‖ₑ^((2:ℝ≥0∞).toReal) < ∞`, and `‖g z‖ₑ^(2:ℝ) = (‖g z‖₊:ℝ≥0∞)^2`.
    rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num] at hlt
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hlt)
    refine lintegral_congr (fun z => ?_)
    rw [enorm_eq_nnnorm, ← ENNReal.rpow_natCast (‖g z‖₊ : ℝ≥0∞) 2]
    norm_num
  have hgxsqfin : (∫⁻ z in K, (‖gx z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := hsqfin hgxK
  have hgysqfin : (∫⁻ z in K, (‖gy z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := hsqfin hgyK
  -- The a.e. bound, restricted to `K`.
  have hbound_K : (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2)
      ≤ᵐ[volume.restrict K]
      fun z => 2 * ((‖gx z‖₊ : ℝ≥0∞) ^ 2 + (‖gy z‖₊ : ℝ≥0∞) ^ 2) := by
    refine (ae_restrict_of_ae ?_)
    filter_upwards [hbound] with z hz
    calc (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2
        ≤ ((‖gx z‖₊ : ℝ≥0∞) + (‖gy z‖₊ : ℝ≥0∞)) ^ 2 := by gcongr
      _ ≤ 2 * ((‖gx z‖₊ : ℝ≥0∞) ^ 2 + (‖gy z‖₊ : ℝ≥0∞) ^ 2) := by
          have hkey := ENNReal.rpow_add_le_mul_rpow_add_rpow
            (‖gx z‖₊ : ℝ≥0∞) (‖gy z‖₊ : ℝ≥0∞) (by norm_num : (1 : ℝ) ≤ 2)
          have htwo : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by
            norm_num
          rw [htwo] at hkey
          rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_natCast (‖gx z‖₊ : ℝ≥0∞) 2,
            ← ENNReal.rpow_natCast (‖gy z‖₊ : ℝ≥0∞) 2]
          push_cast
          exact hkey
  -- Chain: `∫⁻ ball ‖fderiv‖² ≤ ∫⁻ K ‖fderiv‖² ≤ ∫⁻ K 2(‖gx‖²+‖gy‖²) < ∞`.
  have hball_sub_K : Metric.ball (0 : ℂ) R ⊆ K := Metric.ball_subset_closedBall
  -- AE-measurability of `‖gx‖²`, `‖gy‖²` (from `MemLp`'s `AEStronglyMeasurable`).
  have hgxsq_aem : AEMeasurable (fun z => (‖gx z‖₊ : ℝ≥0∞) ^ 2) (volume.restrict K) :=
    (hgxK.aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hgysq_aem : AEMeasurable (fun z => (‖gy z‖₊ : ℝ≥0∞) ^ 2) (volume.restrict K) :=
    (hgyK.aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hfin : (∫⁻ z in K, (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae hbound_K) ?_)
    rw [lintegral_const_mul' 2 _ (by norm_num)]
    rw [lintegral_add_left' hgxsq_aem]
    refine ENNReal.mul_lt_top (by norm_num) ?_
    exact ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hgxsqfin, lt_of_le_of_ne le_top hgysqfin⟩
  exact ne_of_lt (lt_of_le_of_lt (lintegral_mono_set hball_sub_K) (lt_of_le_of_ne le_top hfin))

/-- **`G := ‖Df‖` is square-integrable on every ball.** `IsQCAnalytic` wrapper of
`lintegralSq_fderiv_ball_ne_top_of_memW12loc`: continuity is `hf.1.1.continuous`, a.e.
differentiability is Gehring–Lehto (`IsQCAnalytic.ae_differentiableAt`), and `MemW12loc` is
the field `hf.2.1`. -/
theorem IsQCAnalytic.lintegralSq_fderiv_ball_ne_top {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (R : ℝ) :
    (∫⁻ z in Metric.ball (0 : ℂ) R, (‖fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2) ≠ ∞ :=
  lintegralSq_fderiv_ball_ne_top_of_memW12loc hf.1.1.continuous
    (IsQCAnalytic.ae_differentiableAt hf) hf.2.1 R

/-- **The unbounded-image exceptional curves have zero modulus.** The curves `γ`
of a family `Γ` along which the gradient line integral `∫₀¹ G(γ t)‖γ' t‖ dt` is
infinite *and whose trace `γ '' [0,1]` is contained in no ball* form a zero-modulus
family.

This is the one piece of the localization argument that
`curveModulus_lineIntegral_top_zero` cannot supply on its own, because `Γ` is an
**arbitrary** `Set (ℝ → ℂ)`. The localized truncation `G·𝟙_{ball 0 n}` is
admissible only for curves whose trace lies in a fixed ball; for a curve with
genuinely unbounded trace on `[0,1]` there is no such ball, and the construction
breaks. In every intended application the curve family consists of **continuous**
curves on `[0,1]` (e.g. `Quadrilateral.curveFamily`), for which `γ '' [0,1]` is
compact, hence bounded, so this subfamily is *empty* and the modulus is trivially
`0`. The statement therefore carries a continuity/boundedness hypothesis `hcont` on `Γ`. -/
theorem curveModulus_lineIntegral_top_unbounded_zero {f : ℂ → ℂ}
    (Γ : Set (ℝ → ℂ)) (hcont : ∀ γ ∈ Γ, Continuous γ) :
    curveModulus {γ ∈ Γ |
      arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ = ∞ ∧
        ∀ n : ℕ, ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ Metric.ball (0 : ℂ) n} = 0 := by
  -- Under the continuity hypothesis the subfamily is **empty**: a continuous curve
  -- restricted to the compact interval `[0,1]` has a compact, hence bounded, image,
  -- so its trace lies in some ball `ball 0 n` — contradicting unboundedness.
  have hempty : {γ ∈ Γ |
      arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ = ∞ ∧
        ∀ n : ℕ, ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ Metric.ball (0 : ℂ) n} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro γ ⟨hγΓ, -, hunbdd⟩
    -- The image of the compact interval `[0,1]` under the continuous `γ` is compact.
    have hcompact : IsCompact (γ '' Set.Icc (0 : ℝ) 1) :=
      (isCompact_Icc).image (hcont γ hγΓ)
    -- A compact set is bounded, hence contained in some ball `ball 0 n`.
    obtain ⟨r, hr⟩ := hcompact.isBounded.subset_ball (0 : ℂ)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    -- The unboundedness condition gives a point of the trace outside `ball 0 n`.
    obtain ⟨t, ht, htnotin⟩ := hunbdd n
    have hmem : γ t ∈ γ '' Set.Icc (0 : ℝ) 1 := ⟨t, ht, rfl⟩
    have hin_ball : γ t ∈ Metric.ball (0 : ℂ) r := hr hmem
    apply htnotin
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_ball, dist_zero_right] at hin_ball
    calc ‖γ t‖ < r := hin_ball
      _ < n := hn
  rw [hempty]
  -- `curveModulus ∅ = 0`: the zero density is (vacuously) admissible for `∅`.
  refine le_antisymm ?_ (zero_le)
  have hadm0 : IsAdmissibleDensity (fun _ => (0 : ℝ≥0∞)) (∅ : Set (ℝ → ℂ)) :=
    ⟨measurable_const, fun γ hγ => absurd hγ (Set.notMem_empty γ)⟩
  refine le_trans (iInf₂_le (fun _ => (0 : ℝ≥0∞)) hadm0) ?_
  simp

/-- **(F1) The infinite-gradient-line-integral family has zero modulus.** For a
`W^{1,2}_loc` quasiconformal map `f`, with `G z := ‖fderiv ℝ f z‖₊` the operator
norm of its differential (which lies in `L²_loc` since `f ∈ W^{1,2}_loc`), the
curves `γ` along which the arc-length integral `∫₀¹ G(γ t)‖γ' t‖ dt` of `G` is
infinite form a family of zero modulus.

This is the analytic heart of Fuglede's theorem.  The energy estimate needs the
*global* square-integrability `∫⁻ G² < ∞`, but `MemW12loc f` only gives `G ∈ L²`
on every ball.  The proof localizes:

* For each `n`, the *truncated* density `Gₙ := 𝟙_{ball 0 n}·G` has finite energy
  `∫⁻ Gₙ² = ∫⁻_{ball 0 n} G² < ∞` (`IsQCAnalytic.lintegralSq_fderiv_ball_ne_top`).
  Along a curve `γ` whose trace `γ '' [0,1]` lies in `ball 0 n`, the line integral
  of `Gₙ` equals that of `G`, hence is `∞`.  So
  `curveModulus_zero_of_lintegralSq_finite` gives zero modulus for the subfamily
  `Δₙ := {γ ∈ Γ | line integral of G is ∞, trace ⊆ ball 0 n}`.
* The countable union `⋃ₙ Δₙ` is the bounded-trace part of the exceptional family;
  it has zero modulus by `curveModulus_iUnion_zero`.
* The unbounded-trace part has zero modulus by
  `curveModulus_lineIntegral_top_unbounded_zero` (which for the continuous curve
  families of the applications is empty).

The exceptional family is the union of these two parts, so `curveModulus_mono`
plus `curveModulus_union_zero` finish.  The two genuine analytic inputs are the
ball-energy bound (the strong-`fderiv` ⇄ weak-gradient a.e. bridge) and countable
subadditivity.

De-gated form: stated over the explicit hypothesis triple (continuity + a.e.
differentiability + `MemW12loc`); the `IsQCAnalytic` wrapper is
`curveModulus_lineIntegral_top_zero` below. -/
theorem curveModulus_lineIntegral_top_zero_of_memW12loc {f : ℂ → ℂ}
    (hfcont : Continuous f) (hdiff : ∀ᵐ z, DifferentiableAt ℝ f z) (hW12 : MemW12loc f)
    (Γ : Set (ℝ → ℂ)) (hcont : ∀ γ ∈ Γ, Continuous γ) :
    curveModulus {γ ∈ Γ |
      arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ = ∞} = 0 := by
  classical
  -- The gradient density `G`, and its measurability.
  set G : ℂ → ℝ≥0∞ := fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞) with hG
  have hGmeas : Measurable G := by
    rw [hG]
    exact ((measurable_fderiv ℝ f).nnnorm).coe_nnreal_ennreal
  -- The full exceptional family.
  set E : Set (ℝ → ℂ) := {γ ∈ Γ | arcLengthLineIntegral G γ = ∞} with hE
  -- The `n`-th bounded-trace truncated density `Gₙ := 𝟙_{ball 0 n}·G`.
  set Gn : ℕ → ℂ → ℝ≥0∞ :=
    fun n => (Metric.ball (0 : ℂ) n).indicator G with hGn
  have hGnmeas : ∀ n, Measurable (Gn n) := fun n =>
    hGmeas.indicator measurableSet_ball
  -- The `n`-th bounded-trace subfamily.
  set Δ : ℕ → Set (ℝ → ℂ) :=
    fun n => {γ ∈ Γ | arcLengthLineIntegral G γ = ∞ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Metric.ball (0 : ℂ) n} with hΔ
  -- Each `Δ n` has zero modulus, via the finite-energy reduction applied to `Gₙ`.
  have hΔzero : ∀ n, curveModulus (Δ n) = 0 := by
    intro n
    -- `Gₙ` has finite energy: `∫⁻ Gₙ² = ∫⁻_{ball 0 n} G² < ∞`.
    have hGnfin : ∫⁻ z, (Gn n z) ^ 2 ≠ ∞ := by
      have hpt : (fun z => (Gn n z) ^ 2)
          = (Metric.ball (0 : ℂ) n).indicator (fun z => (G z) ^ 2) := by
        funext z
        by_cases hz : z ∈ Metric.ball (0 : ℂ) (n : ℝ)
        · simp only [hGn, Set.indicator_of_mem hz]
        · simp only [hGn, Set.indicator_of_notMem hz]; norm_num
      rw [hpt, lintegral_indicator measurableSet_ball]
      exact lintegralSq_fderiv_ball_ne_top_of_memW12loc hfcont hdiff hW12 (n : ℝ)
    -- Along every `γ ∈ Δ n`, the line integral of `Gₙ` is `∞` (it equals that of `G`).
    have hΔinf : ∀ γ ∈ Δ n, arcLengthLineIntegral (Gn n) γ = ∞ := by
      rintro γ ⟨-, hγinf, hγtrace⟩
      have heq : arcLengthLineIntegral (Gn n) γ = arcLengthLineIntegral G γ := by
        unfold arcLengthLineIntegral
        refine setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
        have : Gn n (γ t) = G (γ t) := by
          simp only [hGn, Set.indicator_of_mem (hγtrace t ht)]
        rw [this]
      rw [heq, hγinf]
    exact curveModulus_zero_of_lintegralSq_finite (hGnmeas n) hGnfin hΔinf
  -- The bounded-trace part `⋃ₙ Δ n` has zero modulus.
  have hUnionZero : curveModulus (⋃ n, Δ n) = 0 := curveModulus_iUnion_zero hΔzero
  -- The unbounded-trace part.
  set U : Set (ℝ → ℂ) := {γ ∈ Γ | arcLengthLineIntegral G γ = ∞ ∧
      ∀ n : ℕ, ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ Metric.ball (0 : ℂ) n} with hU
  have hUzero : curveModulus U = 0 := curveModulus_lineIntegral_top_unbounded_zero Γ hcont
  -- The exceptional family is contained in `(⋃ₙ Δ n) ∪ U`.
  have hsub : E ⊆ (⋃ n, Δ n) ∪ U := by
    rintro γ ⟨hγΓ, hγinf⟩
    by_cases hb : ∀ n : ℕ, ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ Metric.ball (0 : ℂ) n
    · -- Unbounded trace: `γ ∈ U`.
      exact Or.inr ⟨hγΓ, hγinf, hb⟩
    · -- Bounded trace: some `n` contains the whole trace, so `γ ∈ Δ n`.
      rw [not_forall] at hb
      obtain ⟨n, hn⟩ := hb
      refine Or.inl (Set.mem_iUnion.mpr ⟨n, hγΓ, hγinf, fun t ht => ?_⟩)
      by_contra hnotin
      exact hn ⟨t, ht, hnotin⟩
  -- Conclude by monotonicity and binary subadditivity.
  refine le_antisymm ?_ (zero_le)
  calc curveModulus E
      ≤ curveModulus ((⋃ n, Δ n) ∪ U) := curveModulus_mono hsub
    _ = 0 := curveModulus_union_zero hUnionZero hUzero

/-- **(F1) The infinite-gradient-line-integral family has zero modulus.** `IsQCAnalytic`
wrapper of `curveModulus_lineIntegral_top_zero_of_memW12loc`. -/
theorem curveModulus_lineIntegral_top_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (Γ : Set (ℝ → ℂ)) (hcont : ∀ γ ∈ Γ, Continuous γ) :
    curveModulus {γ ∈ Γ |
      arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ = ∞} = 0 :=
  curveModulus_lineIntegral_top_zero_of_memW12loc hf.1.1.continuous
    (IsQCAnalytic.ae_differentiableAt hf) hf.2.1 Γ hcont

/-- The real arc-length integrand `g t := ‖fderiv ℝ f (γ t)‖ · ‖deriv γ t‖`, the
`ℝ`-valued density whose finiteness drives the Fuglede absolute-continuity
argument. Its `ℝ≥0∞`-coercion is the integrand of `arcLengthLineIntegral`. -/
noncomputable def fdNormMulDeriv (f : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖fderiv ℝ f (γ t)‖ * ‖deriv γ t‖

/-- **(ℂ-valued fundamental theorem of calculus for absolutely continuous curves.)**
If `h : ℝ → ℂ` is absolutely continuous on `uIcc a c`, has a pointwise a.e. derivative
`h'`, and `h'` is interval-integrable on `a..c`, then `h c - h a = ∫ t in a..c, h' t`.

This is the complex-valued analogue of Mathlib's real
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`, obtained componentwise: the
real and imaginary parts `Complex.reCLM ∘ h`, `Complex.imCLM ∘ h` are absolutely
continuous (Lipschitz composition) with a.e. derivatives `(h' ·).re`, `(h' ·).im`, so
the real FTC applies to each part and recombines through `Complex.re_add_im`. -/
private theorem complex_ac_ftc {h h' : ℝ → ℂ} {a c : ℝ}
    (hac : AbsolutelyContinuousOnInterval h a c)
    (hderiv : ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.uIoc a c)),
      HasDerivAt h (h' t) t)
    (hint : IntervalIntegrable h' MeasureTheory.volume a c) :
    h c - h a = ∫ t in a..c, h' t := by
  -- Lipschitz-composition: real/imaginary parts of an AC curve are AC.
  have hLipComp : ∀ {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (K : NNReal),
      LipschitzWith K l → AbsolutelyContinuousOnInterval (fun t => l (h t)) a c := by
    intro Y _ l K hl
    rw [absolutelyContinuousOnInterval_iff] at hac ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hac (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (l (h (E.2 i).1)) (l (h (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (h (E.2 i).1) (h (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (h (E.2 i).1) (h (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  have hre_ac : AbsolutelyContinuousOnInterval (fun t => (h t).re) a c :=
    hLipComp Complex.reCLM ‖Complex.reCLM‖₊ Complex.reCLM.lipschitz
  have him_ac : AbsolutelyContinuousOnInterval (fun t => (h t).im) a c :=
    hLipComp Complex.imCLM ‖Complex.imCLM‖₊ Complex.imCLM.lipschitz
  -- a.e. derivatives of the real/imaginary parts (compose with the `ℝ`-linear CLMs
  -- `reCLM`, `imCLM`).
  have hre_deriv : ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.uIoc a c)),
      HasDerivAt (fun s => (h s).re) (h' t).re t := by
    filter_upwards [hderiv] with t ht
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ht
    simpa using! this
  have him_deriv : ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.uIoc a c)),
      HasDerivAt (fun s => (h s).im) (h' t).im t := by
    filter_upwards [hderiv] with t ht
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t ht
    simpa using! this
  -- Identify the a.e. `deriv` of each part with the corresponding component of `h'`.
  have hre_deriv_eq : ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.uIoc a c)),
      deriv (fun s => (h s).re) t = (h' t).re := by
    filter_upwards [hre_deriv] with t ht using ht.deriv
  have him_deriv_eq : ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.uIoc a c)),
      deriv (fun s => (h s).im) t = (h' t).im := by
    filter_upwards [him_deriv] with t ht using ht.deriv
  -- Real FTC on each part.
  have hre_ftc : ∫ t in a..c, deriv (fun s => (h s).re) t = (h c).re - (h a).re :=
    hre_ac.integral_deriv_eq_sub
  have him_ftc : ∫ t in a..c, deriv (fun s => (h s).im) t = (h c).im - (h a).im :=
    him_ac.integral_deriv_eq_sub
  -- Integrability of the components for the integral-congruence rewrite.
  have hint_re : IntervalIntegrable (fun t => (h' t).re) MeasureTheory.volume a c :=
    ⟨Complex.reCLM.integrable_comp hint.1, Complex.reCLM.integrable_comp hint.2⟩
  have hint_im : IntervalIntegrable (fun t => (h' t).im) MeasureTheory.volume a c :=
    ⟨Complex.imCLM.integrable_comp hint.1, Complex.imCLM.integrable_comp hint.2⟩
  -- Replace the `deriv (… .re)` integrand by `(h' ·).re` under the integral sign.
  have hre_congr : (∫ t in a..c, deriv (fun s => (h s).re) t) = ∫ t in a..c, (h' t).re :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [(ae_restrict_iff' measurableSet_uIoc).mp hre_deriv_eq]
        with t ht hmem using ht hmem)
  have him_congr : (∫ t in a..c, deriv (fun s => (h s).im) t) = ∫ t in a..c, (h' t).im :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [(ae_restrict_iff' measurableSet_uIoc).mp him_deriv_eq]
        with t ht hmem using ht hmem)
  have hre_int : ∫ t in a..c, (h' t).re = (h c).re - (h a).re := by
    rw [← hre_congr, hre_ftc]
  have him_int : ∫ t in a..c, (h' t).im = (h c).im - (h a).im := by
    rw [← him_congr, him_ftc]
  -- The real and imaginary parts of `∫ h'` are `∫ (h'·).re`, `∫ (h'·).im`.
  have hintre : (∫ t in a..c, h' t).re = ∫ t in a..c, (h' t).re := by
    have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint
    simpa using this.symm
  have hintim : (∫ t in a..c, h' t).im = ∫ t in a..c, (h' t).im := by
    have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM hint
    simpa using this.symm
  -- Conclude `h c - h a = ∫ h'` componentwise.
  apply Complex.ext
  · rw [Complex.sub_re, hintre, hre_int]
  · rw [Complex.sub_im, hintim, him_int]

/-- **(Interval-integrability of the derivative of an absolutely continuous curve.)**
If `γ : ℝ → ℂ` is absolutely continuous on every interval, then its derivative `deriv γ`
is interval-integrable on `a..b`.

Componentwise: `Complex.reCLM ∘ γ`, `Complex.imCLM ∘ γ` are real absolutely continuous
(Lipschitz composition), so Mathlib's
`AbsolutelyContinuousOnInterval.intervalIntegrable_deriv` makes their derivatives
interval-integrable; these agree a.e. with `(deriv γ ·).re`, `(deriv γ ·).im`, which
recombine to `deriv γ`. -/
private theorem intervalIntegrable_deriv_of_complex_ac {γ : ℝ → ℂ}
    (hγac : AbsolutelyContinuousOnInterval γ 0 1) (a b : ℝ)
    (hab : Set.uIcc a b ⊆ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (deriv γ) MeasureTheory.volume a b := by
  -- a.e. differentiability of `γ` on `uIcc a b` (bounded variation ⇒ a.e. differentiable).
  have hγ_diff : ∀ᵐ t : ℝ, t ∈ Set.uIcc a b → DifferentiableAt ℝ γ t :=
    (hγac.mono_subinterval hab).boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  -- Lipschitz-composition: real/imaginary parts of `γ` are AC.
  have hLipComp : ∀ {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (K : NNReal),
      LipschitzWith K l → AbsolutelyContinuousOnInterval (fun t => l (γ t)) a b := by
    intro Y _ l K hl
    have hγab := hγac.mono_subinterval hab
    rw [absolutelyContinuousOnInterval_iff] at hγab ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hγab (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (l (γ (E.2 i).1)) (l (γ (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (γ (E.2 i).1) (γ (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (γ (E.2 i).1) (γ (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  have hre_ac : AbsolutelyContinuousOnInterval (fun t => (γ t).re) a b :=
    hLipComp Complex.reCLM ‖Complex.reCLM‖₊ Complex.reCLM.lipschitz
  have him_ac : AbsolutelyContinuousOnInterval (fun t => (γ t).im) a b :=
    hLipComp Complex.imCLM ‖Complex.imCLM‖₊ Complex.imCLM.lipschitz
  -- Real-part / imaginary-part derivatives are interval-integrable.
  have hre_int : IntervalIntegrable (deriv (fun t => (γ t).re)) MeasureTheory.volume a b :=
    hre_ac.intervalIntegrable_deriv
  have him_int : IntervalIntegrable (deriv (fun t => (γ t).im)) MeasureTheory.volume a b :=
    him_ac.intervalIntegrable_deriv
  -- a.e. on `uIcc a b`: `deriv (re∘γ) = (deriv γ).re` and `deriv (im∘γ) = (deriv γ).im`.
  have hre_eq : (deriv (fun t => (γ t).re)) =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
      (fun t => (deriv γ t).re) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hγ_diff] with t ht ht'
    have hd : HasDerivAt γ (deriv γ t) t := (ht (Set.uIoc_subset_uIcc ht')).hasDerivAt
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
    simpa using! this.deriv
  have him_eq : (deriv (fun t => (γ t).im)) =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
      (fun t => (deriv γ t).im) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hγ_diff] with t ht ht'
    have hd : HasDerivAt γ (deriv γ t) t := (ht (Set.uIoc_subset_uIcc ht')).hasDerivAt
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd
    simpa using! this.deriv
  -- Transport interval-integrability to the components of `deriv γ`.
  have hre_int' : IntervalIntegrable (fun t => (deriv γ t).re) MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff]
    exact (hre_int.def'.congr hre_eq)
  have him_int' : IntervalIntegrable (fun t => (deriv γ t).im) MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff]
    exact (him_int.def'.congr him_eq)
  -- Push the real components into `ℂ` via `Complex.ofRealCLM`.
  have hre_intℂ : IntervalIntegrable (fun t => (↑(deriv γ t).re : ℂ)) MeasureTheory.volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp hre_int'.1, Complex.ofRealCLM.integrable_comp hre_int'.2⟩
  have him_intℂ : IntervalIntegrable (fun t => (↑(deriv γ t).im : ℂ)) MeasureTheory.volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp him_int'.1, Complex.ofRealCLM.integrable_comp him_int'.2⟩
  -- Recombine: `deriv γ = (re) + (im) * I`.
  have hrecomb : deriv γ = fun t => (↑(deriv γ t).re : ℂ) + (↑(deriv γ t).im : ℂ) * Complex.I := by
    funext t; exact (Complex.re_add_im (deriv γ t)).symm
  rw [hrecomb]
  exact hre_intℂ.add (him_intℂ.mul_const Complex.I)

/-- **(Smooth upper-gradient bound.)** For a `C¹` function `g : ℂ → ℂ`
and an absolutely continuous curve `γ`, the distance `g` moves across `uIoc x y` is
bounded by the arc-length integral of `‖fderiv ℝ g‖` along the curve.

This is the per-mollifier elementary bound: `g ∘ γ` is `C¹ ∘ AC`, hence AC, with a.e.
derivative `(fderiv ℝ g (γ t)) (deriv γ t)` (chain rule); the ℂ-valued FTC
(`complex_ac_ftc`) plus `norm_integral_le_integral_norm` and the operator-norm bound
`‖(fderiv ℝ g (γ t)) (deriv γ t)‖ ≤ ‖fderiv ℝ g (γ t)‖ · ‖deriv γ t‖` give the claim. -/
theorem dist_comp_le_setIntegral_of_contDiff {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    {γ : ℝ → ℂ} (hγcont : Continuous γ)
    (hγac : AbsolutelyContinuousOnInterval γ 0 1)
    (x y : ℝ) (hxy : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 1) :
    dist (g (γ x)) (g (γ y)) ≤ ∫ t in Set.uIoc x y, ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖ := by
  -- `g` is differentiable with continuous derivative, hence `HasFDerivAt g (fderiv) z`.
  have hgdiff : ∀ z : ℂ, HasFDerivAt g (fderiv ℝ g z) z :=
    fun z => (hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  -- a.e. derivative of `γ` on `uIoc x y ⊆ [0,1]`: AC on `[0,1]` ⇒ differentiable a.e.
  -- there, and `deriv` witnesses it.
  have hγ_deriv : ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.uIoc x y)),
      HasDerivAt γ (deriv γ t) t := by
    have hbv : BoundedVariationOn γ (Set.uIcc (0 : ℝ) 1) := hγac.boundedVariationOn
    have hdiff01 : ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
        DifferentiableAt ℝ γ t := by
      rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hbv.ae_differentiableAt_of_mem_uIcc] with t ht htmem
      exact ht (by rw [Set.uIcc_of_le (by norm_num)]; exact htmem)
    have hsub : MeasureTheory.volume.restrict (Set.uIoc x y) ≤
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1) :=
      Measure.restrict_mono (Set.uIoc_subset_uIcc.trans hxy) le_rfl
    filter_upwards [hsub.absolutelyContinuous hdiff01] with t ht using ht.hasDerivAt
  -- The composed curve `g ∘ γ`, its a.e. derivative, integrability of the integrand,
  -- and the ℂ-valued FTC, are assembled below.
  set G : ℝ → ℂ := fun t => g (γ t) with hG
  set G' : ℝ → ℂ := fun t => (fderiv ℝ g (γ t)) (deriv γ t) with hG'
  -- a.e. chain rule: `HasDerivAt (g ∘ γ) ((fderiv g (γ t)) (deriv γ t)) t` on `uIoc x y`.
  have hG_deriv : ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.uIoc x y)),
      HasDerivAt G (G' t) t := by
    filter_upwards [hγ_deriv] with t ht
    exact (hgdiff (γ t)).comp_hasDerivAt t ht
  -- `g ∘ γ` is AC on `uIcc x y`: `g` is Lipschitz on a ball containing the compact
  -- trace `γ '' uIcc x y`, and Lipschitz-on-set ∘ AC is AC.
  have hG_ac : AbsolutelyContinuousOnInterval G x y := by
    -- A closed ball `closedBall 0 R` containing the compact trace `γ '' uIcc x y`.
    have htrace_cpt : IsCompact (γ '' Set.uIcc x y) := (isCompact_uIcc).image hγcont
    obtain ⟨R, hRpos, hRsub⟩ : ∃ R > 0, γ '' Set.uIcc x y ⊆ Metric.closedBall (0 : ℂ) R := by
      obtain ⟨R, hRsub⟩ := htrace_cpt.isBounded.subset_closedBall (0 : ℂ)
      exact ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _),
        hRsub.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
    -- `g` is `K`-Lipschitz on the (convex, compact) ball.
    obtain ⟨K, hK⟩ : ∃ K, LipschitzOnWith K g (Metric.closedBall (0 : ℂ) R) :=
      (hg.contDiffOn).exists_lipschitzOnWith (by norm_num) (convex_closedBall _ _)
        (isCompact_closedBall _ _)
    -- Lipschitz-on-trace ∘ AC ⇒ AC, by the ε–δ bound on distances.
    have hγxy := hγac.mono_subinterval hxy
    rw [absolutelyContinuousOnInterval_iff] at hγxy ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hγxy (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    -- Each endpoint of a disjoint subinterval inside `uIcc x y` lands in the ball.
    have hmem : ∀ s : ℝ, s ∈ Set.uIcc x y → γ s ∈ Metric.closedBall (0 : ℂ) R :=
      fun s hs => hRsub ⟨s, hs, rfl⟩
    have hsubmem := hE.1
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (g (γ (E.2 i).1)) (g (γ (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (γ (E.2 i).1) (γ (E.2 i).2) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact hK.dist_le_mul _ (hmem _ (hsubmem i hi).1) _ (hmem _ (hsubmem i hi).2)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (γ (E.2 i).1) (γ (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- `fderiv ℝ g` is continuous (`g` is `C¹`), so `t ↦ ‖fderiv ℝ g (γ t)‖` is continuous.
  have hfd_cont : Continuous (fun z => fderiv ℝ g z) := hg.continuous_fderiv (by norm_num)
  have hnormfd_cont : Continuous (fun t => ‖fderiv ℝ g (γ t)‖) :=
    (hfd_cont.comp hγcont).norm
  -- `‖deriv γ ·‖` is interval-integrable (AC ⇒ deriv interval-integrable, then `.norm`).
  have hnormγ'_int : IntervalIntegrable (fun t => ‖deriv γ t‖) MeasureTheory.volume x y :=
    (intervalIntegrable_deriv_of_complex_ac hγac x y hxy).norm
  -- The real density `‖fderiv g (γ ·)‖ · ‖deriv γ ·‖` is interval-integrable on `x..y`.
  have hdens_II : IntervalIntegrable (fun t => ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖)
      MeasureTheory.volume x y :=
    hnormγ'_int.continuousOn_mul hnormfd_cont.continuousOn
  -- Measurability of the ℂ-valued derivative `G'`: the bilinear application
  -- `(L, v) ↦ L v` is continuous, `fderiv g ∘ γ` is continuous, `deriv γ` is measurable.
  have hG'_meas : Measurable G' := by
    have happ : Continuous (fun p : (ℂ →L[ℝ] ℂ) × ℂ => p.1 p.2) :=
      isBoundedBilinearMap_apply.continuous
    have hpair : Measurable (fun t => ((fderiv ℝ g (γ t)), deriv γ t)) :=
      (hfd_cont.comp hγcont).measurable.prodMk (measurable_deriv γ)
    exact happ.measurable.comp hpair
  -- Domination: `‖G'‖ ≤ ‖fderiv g (γ)‖ ‖γ'‖`, so `G'` is interval-integrable.
  have hG'_int : IntervalIntegrable G' MeasureTheory.volume x y :=
    hdens_II.mono_fun' hG'_meas.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ (fun t => (fderiv ℝ g (γ t)).le_opNorm (deriv γ t)))
  -- ℂ-valued FTC for `G = g ∘ γ`.
  have hftc : G y - G x = ∫ t in x..y, G' t := complex_ac_ftc hG_ac hG_deriv hG'_int
  -- The pointwise norm bound `‖G' t‖ ≤ ‖fderiv g (γ t)‖ · ‖deriv γ t‖`.
  have hptbd : ∀ t, ‖G' t‖ ≤ ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖ :=
    fun t => (fderiv ℝ g (γ t)).le_opNorm (deriv γ t)
  -- `dist (g (γ x)) (g (γ y)) = ‖G y - G x‖ ≤ ∫_{Ι} ‖G'‖ ≤ ∫_{Ι} ‖fderiv g (γ)‖ ‖γ'‖`.
  have hdist : dist (g (γ x)) (g (γ y)) = ‖∫ t in x..y, G' t‖ := by
    rw [dist_comm, dist_eq_norm, ← hftc]
  rw [hdist]
  -- `‖G'‖` is interval-integrable, and the real density is integrable on `uIoc x y`.
  have hnorm_int : IntervalIntegrable (fun t => ‖G' t‖) MeasureTheory.volume x y :=
    hG'_int.norm
  have hdens_int : IntegrableOn (fun t => ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖)
      (Set.uIoc x y) MeasureTheory.volume := hdens_II.def'
  calc ‖∫ t in x..y, G' t‖
      ≤ ∫ t in Set.uIoc x y, ‖G' t‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ t in Set.uIoc x y, ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖ :=
        MeasureTheory.setIntegral_mono_on hnorm_int.def' hdens_int measurableSet_uIoc
          (fun t _ => hptbd t)

open scoped Pointwise in
/-- **(L² mollification convergence — scalar core.)** For `g ∈ L²(ℂ)` and a sequence
of normed `ContDiffBump`s on `ℂ` with outer radius tending to `0`, the mollifications
`(φ n).normed volume ⋆ g` converge to `g` in `L²`.

This is the classical `3·ε` argument. Approximate `g` in `L²` by a smooth compactly
supported `h` with `eLpNorm (g - h) 2 ≤ ε` (`MemLp.exist_eLpNorm_sub_le`). For the
smooth compactly supported `h`, the mollifications converge uniformly with support in
a fixed compact set (`ContDiffBump.convolution_tendsto_right_of_continuous` plus the
shrinking support `rOut → 0`), so `eLpNorm (ρ_n ⋆ h - h) 2 → 0`. For the error term,
write the real normed bump as a complex-valued `L¹` function (`r • z = (↑r) * z`, so
the `lsmul ℝ ℝ` convolution equals the `mul ℂ ℂ` convolution of the cast bump) and
apply Young's inequality `eLpNorm_convolution_le`: `eLpNorm (ρ_n ⋆ (g - h)) 2 ≤
eLpNorm (↑ρ_n) 1 · eLpNorm (g - h) 2 = ε`, since the bump has unit `L¹` mass
(`ContDiffBump.integral_normed`). Conclude by the triangle inequality. -/
theorem eLpNorm_convolution_normed_sub_tendsto_zero {g : ℂ → ℂ}
    (hg : MemLp g 2 MeasureTheory.volume) (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφrout : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm
        (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) g
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume - g) 2 MeasureTheory.volume)
      Filter.atTop (nhds 0) := by
  classical
  -- `ρ n := (φ n).normed volume`, and `C n := ρ n ⋆ g`.
  set Cg : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed MeasureTheory.volume)
    g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with hCg
  -- ********** (P1) Smooth compactly supported approximant. **********
  -- We will repeat the `ε/3` argument for each `ε`; first, the `ε`-independent piece
  -- (P3) below is proved once, as a `Tendsto` statement.
  -- ====================================================================
  -- (P3) `ρ n ⋆ h - h → 0` in `L²` for a fixed smooth compactly supported `h`.
  -- ====================================================================
  have hP3 : ∀ (h : ℂ → ℂ), HasCompactSupport h → ContDiff ℝ (⊤ : ℕ∞) h →
      Filter.Tendsto (fun n => eLpNorm
        (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) h
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume - h) 2 MeasureTheory.volume)
        Filter.atTop (nhds 0) := by
    intro h hh_supp hh_smooth
    obtain ⟨M, hM⟩ := hh_smooth.continuous.bounded_above_of_compact_support hh_supp
    have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
    -- Fixed compact set `Kset := cthickening 1 (tsupport h)`.
    set Kset : Set ℂ := Metric.cthickening 1 (tsupport h) with hKdef
    have hKcompact : IsCompact Kset := hh_supp.isCompact.cthickening
    have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
    have hKfin : MeasureTheory.volume Kset < ⊤ := hKcompact.measure_lt_top
    have htsupp_sub : tsupport h ⊆ Kset := Metric.self_subset_cthickening _
    set Cn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed MeasureTheory.volume)
      h (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with hCn
    -- continuity of each `Cn n`.
    have hCn_cont : ∀ n, Continuous (Cn n) := fun n =>
      HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
    -- pointwise convergence `Cn n x → h x`.
    have hptwise : ∀ x, Filter.Tendsto (fun n => Cn n x) Filter.atTop (nhds (h x)) := fun x =>
      ContDiffBump.convolution_tendsto_right_of_continuous hφrout hh_smooth.continuous x
    -- uniform sup bound `‖Cn n x‖ ≤ M`.
    have hCnbd : ∀ n x, ‖Cn n x‖ ≤ M := by
      intro n x
      set ρ := (φ n).normed MeasureTheory.volume with hρ
      have hρnn : ∀ t, 0 ≤ ρ t := (φ n).nonneg_normed
      rw [hCn]; simp only; rw [MeasureTheory.convolution_def]
      calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t)) ∂MeasureTheory.volume‖
          ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t))‖ ∂MeasureTheory.volume :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ t, ρ t * M ∂MeasureTheory.volume := by
            have hint : Integrable ρ MeasureTheory.volume :=
              ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
                ((φ n).hasCompactSupport_normed)
            apply integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (hint.mul_const M)
            refine Filter.Eventually.of_forall (fun t => ?_)
            simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hρnn t)]
            exact mul_le_mul_of_nonneg_left (hM _) (hρnn t)
        _ = (∫ t, ρ t ∂MeasureTheory.volume) * M := by rw [integral_mul_const]
        _ = M := by rw [(φ n).integral_normed]; ring
    have hMh : ∀ y, ‖h y‖ ≤ M := hM
    -- eventual support control: `support (Cn n) ⊆ Kset` once `(φ n).rOut ≤ 1`.
    have hsupp_in_K : ∀ᶠ n in Filter.atTop, Function.support (Cn n) ⊆ Kset := by
      have hev : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 1 := by
        have := hφrout.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
        filter_upwards [this] with n hn using hn
      filter_upwards [hev] with n hrout1
      have haddsub : Metric.closedBall (0 : ℂ) (φ n).rOut + tsupport h ⊆ Kset := by
        intro z hz
        obtain ⟨a, ha, b, hb, rfl⟩ := hz
        rw [Metric.mem_closedBall, dist_zero_right] at ha
        refine Metric.mem_cthickening_of_dist_le (a + b) b 1 (tsupport h) hb ?_
        rw [dist_eq_norm]; simp only [add_sub_cancel_right]; exact le_trans ha hrout1
      have hsub := MeasureTheory.support_convolution_subset (μ := MeasureTheory.volume)
        (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
        (f := (φ n).normed MeasureTheory.volume) (g := h)
      refine hsub.trans (le_trans ?_ haddsub)
      apply Set.add_subset_add _ (subset_tsupport h)
      intro z hz
      have h1 : z ∈ tsupport ((φ n).normed MeasureTheory.volume) := subset_tsupport _ hz
      rwa [(φ n).tsupport_normed_eq] at h1
    -- finite-measure machinery on `volume.restrict Kset`.
    have : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Kset) := by
      constructor; rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKfin
    set D : ℕ → ℂ → ℂ := fun n => Cn n - h with hD
    -- on the eventual support set, the `L²` norm over `volume` and over `restrict Kset` agree.
    have hrestrict : ∀ᶠ n in Filter.atTop,
        eLpNorm (D n) 2 MeasureTheory.volume
          = eLpNorm (D n) 2 (MeasureTheory.volume.restrict Kset) := by
      filter_upwards [hsupp_in_K] with n hn
      have hDsupp : Function.support (D n) ⊆ Kset := by
        intro x hx
        simp only [hD, Pi.sub_apply, Function.mem_support, ne_eq] at hx
        by_contra hxK
        have h1 : Cn n x = 0 := Function.notMem_support.mp (fun hc => hxK (hn hc))
        have h2 : h x = 0 := Function.notMem_support.mp
          (fun hc => hxK (htsupp_sub (subset_tsupport h hc)))
        rw [h1, h2, sub_zero] at hx; exact hx rfl
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hKmeas, Set.indicator_eq_self.mpr hDsupp]
    -- `L²` convergence on the finite-measure set via Vitali / a.e. convergence.
    have hgoal : Filter.Tendsto (fun n => eLpNorm (D n) 2 (MeasureTheory.volume.restrict Kset))
        Filter.atTop (nhds 0) := by
      have hui : MeasureTheory.UnifIntegrable Cn 2 (MeasureTheory.volume.restrict Kset) := by
        refine MeasureTheory.unifIntegrable_of (by norm_num) (by norm_num)
          (fun n => (hCn_cont n).aestronglyMeasurable) (fun ε hε => ?_)
        refine ⟨(M.toNNReal + 1), fun n => ?_⟩
        have hempty : {x | (M.toNNReal + 1 : ℝ≥0) ≤ ‖Cn n x‖₊} = (∅ : Set ℂ) := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
          have hb' : ‖Cn n x‖₊ ≤ M.toNNReal := by
            rw [← NNReal.coe_le_coe, Real.coe_toNNReal M hM0]; exact hCnbd n x
          exact lt_of_le_of_lt hb' (by simp)
        rw [hempty, Set.indicator_empty]; simp
      have hhmem : MemLp h 2 (MeasureTheory.volume.restrict Kset) :=
        MemLp.of_bound hh_smooth.continuous.aestronglyMeasurable M
          (Filter.Eventually.of_forall hMh)
      exact MeasureTheory.tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
        (fun n => (hCn_cont n).aestronglyMeasurable) hhmem hui
        (Filter.Eventually.of_forall hptwise)
    exact Filter.Tendsto.congr' (hrestrict.mono (fun n hn => hn.symm)) hgoal
  -- ====================================================================
  -- (P2) Young error bound on `ρ n ⋆ u` for `u ∈ L²`.
  -- ====================================================================
  have hP2 : ∀ (u : ℂ → ℂ), MemLp u 2 MeasureTheory.volume → ∀ (ε : ℝ),
      eLpNorm u 2 MeasureTheory.volume ≤ ENNReal.ofReal ε → ∀ n,
        eLpNorm (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) u
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) 2 MeasureTheory.volume
          ≤ ENNReal.ofReal ε := by
    intro u hu ε hclose n
    set ρc : ℂ → ℂ := fun z => (((φ n).normed MeasureTheory.volume z : ℝ) : ℂ) with hρc
    have hconv_eq : MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) u
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
        = MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ) MeasureTheory.volume := by
      funext x
      rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      simp only [hρc, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
      exact (Complex.real_smul).symm
    rw [hconv_eq]
    have hρc_memLp : MemLp ρc 1 MeasureTheory.volume := by
      have hcont : Continuous ρc :=
        Complex.continuous_ofReal.comp ((φ n).contDiff_normed (n := 0)).continuous
      have hsupp : HasCompactSupport ρc :=
        ((φ n).hasCompactSupport_normed).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
      exact hcont.memLp_of_hasCompactSupport hsupp
    have hρc_norm : eLpNorm ρc 1 MeasureTheory.volume = 1 := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      have hint : Integrable ((φ n).normed MeasureTheory.volume) MeasureTheory.volume :=
        ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
          ((φ n).hasCompactSupport_normed)
      have hnn : 0 ≤ᵐ[MeasureTheory.volume] (φ n).normed MeasureTheory.volume :=
        Filter.Eventually.of_forall (fun z => (φ n).nonneg_normed z)
      calc ∫⁻ z, ‖ρc z‖ₑ ∂MeasureTheory.volume
          = ∫⁻ z, ENNReal.ofReal ((φ n).normed MeasureTheory.volume z) ∂MeasureTheory.volume := by
            refine lintegral_congr (fun z => ?_)
            rw [hρc,
              show ‖(((φ n).normed MeasureTheory.volume z : ℝ) : ℂ)‖ₑ
                  = ‖(φ n).normed MeasureTheory.volume z‖ₑ from by
                rw [← enorm_norm, Complex.norm_real, enorm_norm],
              Real.enorm_of_nonneg ((φ n).nonneg_normed z)]
        _ = ENNReal.ofReal (∫ z, (φ n).normed MeasureTheory.volume z ∂MeasureTheory.volume) :=
            (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
        _ = 1 := by rw [(φ n).integral_normed]; simp
    calc eLpNorm (MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ)
            MeasureTheory.volume) 2 MeasureTheory.volume
        ≤ eLpNorm ρc 1 MeasureTheory.volume * eLpNorm u 2 MeasureTheory.volume :=
          eLpNorm_convolution_le hρc_memLp hu
      _ = eLpNorm u 2 MeasureTheory.volume := by rw [hρc_norm, one_mul]
      _ ≤ ENNReal.ofReal ε := hclose
  -- ====================================================================
  -- Main: `∀ ε > 0, ∀ᶠ n, eLpNorm (Cg n - g) 2 ≤ ε`.
  -- ====================================================================
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- pull out a positive real `δ` with `ENNReal.ofReal δ = ε` (use `δ := ε.toReal`).
  by_cases htop : ε = ⊤
  · refine Filter.Eventually.of_forall (fun n => ?_)
    rw [htop]; exact le_top
  set δ : ℝ := ε.toReal with hδ
  have hδpos : 0 < δ := ENNReal.toReal_pos hε.ne' htop
  have hδle : ENNReal.ofReal δ = ε := ENNReal.ofReal_toReal htop
  -- (P1) the smooth approximant `h` with `eLpNorm (g - h) 2 ≤ ofReal (δ/3)`.
  obtain ⟨h, hh_supp, hh_smooth, hh_close⟩ := hg.exist_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (ε := δ / 3) (by positivity)
  -- `MemLp h 2` and `MemLp (g - h) 2`.
  have hh_memLp : MemLp h 2 MeasureTheory.volume :=
    hh_smooth.continuous.memLp_of_hasCompactSupport hh_supp
  have hgh_memLp : MemLp (g - h) 2 MeasureTheory.volume := hg.sub hh_memLp
  -- `eLpNorm (g - h) 2 ≤ ofReal (δ/3)`.
  -- (P2) applied to `u := g - h`.
  have hP2gh : ∀ n, eLpNorm (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume)
        (g - h) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) 2 MeasureTheory.volume
        ≤ ENNReal.ofReal (δ / 3) :=
    hP2 (g - h) hgh_memLp (δ / 3) hh_close
  -- (P3) eventual bound.
  have hP3ev : ∀ᶠ n in Filter.atTop,
      eLpNorm (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) h
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume - h) 2 MeasureTheory.volume
        ≤ ENNReal.ofReal (δ / 3) :=
    (ENNReal.tendsto_nhds_zero.mp (hP3 h hh_supp hh_smooth) (ENNReal.ofReal (δ / 3))
      (ENNReal.ofReal_pos.mpr (by positivity)))
  -- the convolution decomposition `Cg n = ρ n ⋆ (g - h) + ρ n ⋆ h`.
  have hdecomp : ∀ n, Cg n - g = MeasureTheory.convolution ((φ n).normed MeasureTheory.volume)
        (g - h) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
      + (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) h
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume - h) + (h - g) := by
    intro n
    have hce1 : MeasureTheory.ConvolutionExists ((φ n).normed MeasureTheory.volume) (g - h)
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := by
      refine HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous ?_
      exact (hg.locallyIntegrable (by norm_num)).sub hh_smooth.continuous.locallyIntegrable
    have hce2 : MeasureTheory.ConvolutionExists ((φ n).normed MeasureTheory.volume) h
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume :=
      HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
    have hsplit : Cg n = MeasureTheory.convolution ((φ n).normed MeasureTheory.volume)
          (g - h) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
        + MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) h
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := by
      rw [hCg]; simp only
      rw [← MeasureTheory.ConvolutionExists.distrib_add hce1 hce2]
      congr 1; abel
    rw [hsplit]; abel
  -- combine: triangle inequality.
  filter_upwards [hP3ev] with n hn3
  rw [hdecomp n]
  -- measurabilities for `eLpNorm_add_le`.
  have hm1 : AEStronglyMeasurable (MeasureTheory.convolution
      ((φ n).normed MeasureTheory.volume) (g - h) (ContinuousLinearMap.lsmul ℝ ℝ)
      MeasureTheory.volume) MeasureTheory.volume :=
    (HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
      ((φ n).contDiff_normed (n := 0)).continuous
      ((hg.locallyIntegrable (by norm_num)).sub
        hh_smooth.continuous.locallyIntegrable)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (MeasureTheory.convolution
      ((φ n).normed MeasureTheory.volume) h (ContinuousLinearMap.lsmul ℝ ℝ)
      MeasureTheory.volume - h) MeasureTheory.volume :=
    ((HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
      ((φ n).contDiff_normed (n := 0)).continuous
      hh_smooth.continuous.locallyIntegrable).sub hh_smooth.continuous).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (h - g) MeasureTheory.volume :=
    (hh_memLp.sub hg).1
  have hkey : eLpNorm (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume)
        (g - h) (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
      + (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) h
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume - h) + (h - g)) 2
        MeasureTheory.volume
      ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
    refine le_trans (eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)) ?_
    refine add_le_add (le_trans (eLpNorm_add_le hm1 hm2 (by norm_num)) ?_) ?_
    · exact add_le_add (hP2gh n) hn3
    · -- `eLpNorm (h - g) 2 = eLpNorm (g - h) 2 ≤ ofReal (δ/3)`.
      rw [eLpNorm_sub_comm]; exact hh_close
  refine le_trans hkey ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← hδle]
  apply le_of_eq; congr 1; ring

/-- **(A1: mollification commutes with the weak directional derivative.)** If `gv`
is a weak directional derivative of `f` in the real direction `v` (on all of `ℂ`),
then for a smooth compactly supported real mollifier `ρ` the genuine directional
derivative of the (smooth) mollification `ρ ⋆ f` equals the mollification of `gv`:
`(fderiv ℝ (ρ ⋆ f) z) v = (ρ ⋆ gv) z`.

The mollification `ρ ⋆ f` is differentiated by moving the derivative onto the
smooth factor (`HasCompactSupport.hasFDerivAt_convolution_left`):
`(fderiv ℝ (ρ ⋆ f) z) v = ∫ ((fderiv ℝ ρ t) v) • f (z - t) dt`. Substituting
`u = z - t` and setting the test function `φ z (u) := ρ (z - u)` — which is smooth,
compactly supported, and satisfies `(fderiv ℝ (φ z) u) v = -(fderiv ℝ ρ (z - u)) v`
by the chain rule for the affine map `u ↦ z - u` — turns this into
`-∫ ((fderiv ℝ (φ z) u) v) • f u du`. The weak-derivative integration-by-parts
identity `HasWeakDirDeriv` applied to `φ z` rewrites it as `∫ (φ z u) • gv u du =
∫ ρ (z - u) • gv u du`, which is `(ρ ⋆ gv) z` after substituting back. -/
theorem fderiv_convolution_normed_apply_eq {f gv : ℂ → ℂ} {v : ℂ}
    (hv : HasWeakDirDeriv v gv f Set.univ)
    (hf : MeasureTheory.LocallyIntegrable f) (hgv : MeasureTheory.LocallyIntegrable gv)
    {ρ : ℂ → ℝ} (hρ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρ_supp : HasCompactSupport ρ) (z : ℂ) :
    (fderiv ℝ (MeasureTheory.convolution ρ f
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) z) v
      = MeasureTheory.convolution ρ gv
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume z := by
  classical
  -- `gv` is not needed beyond the statement's typing role.
  have _hgv := hgv
  -- Abbreviation for the scalar-multiplication bilinear map.
  set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
  -- `ρ` is `C^1` and continuous (specializations of the `C^∞` hypothesis).
  have hρ_one : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) ρ := hρ_smooth.of_le (by exact_mod_cast le_top)
  have hρ_diff : Differentiable ℝ ρ :=
    hρ_one.differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
  have hρ_cont : Continuous ρ := hρ_smooth.continuous
  -- `fderiv ℝ ρ` has compact support.
  have hdρ_supp : HasCompactSupport (fderiv ℝ ρ) := hρ_supp.fderiv ℝ
  -- (1) Differentiate the mollification onto the smooth factor.
  have hderiv :
      HasFDerivAt (MeasureTheory.convolution ρ f L MeasureTheory.volume)
        (MeasureTheory.convolution (fderiv ℝ ρ) f (L.precompL ℂ) MeasureTheory.volume z) z :=
    HasCompactSupport.hasFDerivAt_convolution_left L hρ_supp hρ_one hf z
  rw [hderiv.fderiv]
  -- (2) Evaluate the vector-valued convolution at `v` and move it inside the integral.
  have hconvexists :
      MeasureTheory.ConvolutionExistsAt (fderiv ℝ ρ) f z (L.precompL ℂ) MeasureTheory.volume :=
    (hdρ_supp.convolutionExists_left (L.precompL ℂ)
      (hρ_one.continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))) hf) z
  rw [MeasureTheory.convolution_def,
      ContinuousLinearMap.integral_apply hconvexists.integrable]
  simp only [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.lsmul_apply]
  -- Now goal: `∫ t, ((fderiv ℝ ρ t) v) • f (z - t) = (ρ ⋆ gv) z`.
  -- (3) Change variables `t ↦ z - t`.
  have hcv :
      (∫ t, ((fderiv ℝ ρ t) v) • f (z - t) ∂MeasureTheory.volume)
        = ∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂MeasureTheory.volume := by
    have hself := MeasureTheory.integral_sub_left_eq_self
      (fun t => ((fderiv ℝ ρ t) v) • f (z - t)) MeasureTheory.volume z
    simp only [sub_sub_cancel] at hself
    exact hself.symm
  refine hcv.trans ?_
  -- (4) Chain rule for the test function `φz u := ρ (z - u)`.
  set φz : ℂ → ℝ := fun u => ρ (z - u) with hφz
  have hφz_fderiv : ∀ u, (fderiv ℝ φz u) v = -((fderiv ℝ ρ (z - u)) v) := by
    intro u
    have hsub : HasFDerivAt (fun u : ℂ => z - u) (-ContinuousLinearMap.id ℝ ℂ) u := by
      simpa using (hasFDerivAt_id u).const_sub z
    have hcomp : HasFDerivAt φz
        ((fderiv ℝ ρ (z - u)).comp (-ContinuousLinearMap.id ℝ ℂ)) u :=
      (hρ_diff (z - u)).hasFDerivAt.comp u hsub
    rw [hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, map_neg]
  have hint_eq :
      (∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂MeasureTheory.volume)
        = -∫ u, ((fderiv ℝ φz u) v) • f u ∂MeasureTheory.volume := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    change ((fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ φz u) v) • f u)
    rw [hφz_fderiv u]
    rw [show (-(fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ ρ (z - u)) v) • f u)
      from neg_smul _ _, neg_neg]
  rw [hint_eq]
  -- (5) Apply the weak-derivative identity to `φz`.
  have hφz_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φz :=
    hρ_smooth.comp (contDiff_const.sub contDiff_id)
  have hφz_supp : HasCompactSupport φz :=
    hρ_supp.comp_homeomorph (Homeomorph.subLeft z)
  have hwd := hv φz hφz_smooth hφz_supp (Set.subset_univ _)
  rw [hwd, neg_neg]
  -- (6) Recognize the convolution `∫ ρ (z - u) • gv u = (ρ ⋆ gv) z`.
  rw [MeasureTheory.convolution_def, ← MeasureTheory.integral_sub_left_eq_self
      (fun t => (L (ρ t)) (gv (z - t))) MeasureTheory.volume z]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only [hφz, sub_sub_cancel, hL, ContinuousLinearMap.lsmul_apply]

/-- **(A: mollified-gradient `L²` energy decay on a ball.)** For a quasiconformal
`f` and a sequence of normed `ContDiffBump` mollifiers with outer radius tending to
`0`, the `L²` energy of the difference between the (genuine) differential of the
mollification `ρ_n ⋆ f` and the differential of `f`, measured over any ball, tends
to `0`.

This assembles the two convolution facts with the weak-to-strong bridge. The weak
gradient of `f ∈ W^{1,2}_loc` provides partials `gx` (direction `1`) and `gy`
(direction `I`), both `L²_loc`. By `fderiv_convolution_normed_apply_eq` the
directional derivatives of `ρ_n ⋆ f` are the mollifications `ρ_n ⋆ gx` and
`ρ_n ⋆ gy`; by `fderiv_ae_eq_weakDirDeriv` the directional derivatives of `f` agree
a.e. with `gx`, `gy`. Truncating `gx`, `gy` to a slightly larger ball makes them
globally `L²`, and on the given ball the mollified truncations agree with the
mollified partials once `rOut < 1`; so the operator-norm bound
`‖T‖ ≤ ‖T 1‖ + ‖T I‖` reduces the energy to the two scalar pieces
`∫ ‖ρ_n ⋆ gx_R - gx_R‖²` and `∫ ‖ρ_n ⋆ gy_R - gy_R‖²`, each tending to `0` by the
scalar `L²` mollification convergence `eLpNorm_convolution_normed_sub_tendsto_zero`.

De-gated form: stated over the explicit hypothesis triple (continuity + a.e.
differentiability + `MemW12loc`); the `IsQCAnalytic` wrapper is
`mollified_fderiv_ball_energy_tendsto_zero` below. -/
theorem mollified_fderiv_ball_energy_tendsto_zero_of_memW12loc {f : ℂ → ℂ}
    (hfcont : Continuous f) (hdiff : ∀ᵐ z, DifferentiableAt ℝ f z) (hW12 : MemW12loc f)
    (R : ℝ) (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφrout : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫⁻ z in Metric.ball (0 : ℂ) R,
        (‖fderiv ℝ (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
            (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) z
          - fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2)
      Filter.atTop (nhds 0) := by
  classical
  -- Abbreviations: `ρ n := (φ n).normed volume`, `fn n := ρ n ⋆ f`.
  set ρ : ℕ → ℂ → ℝ := fun n => (φ n).normed MeasureTheory.volume with hρ
  set fn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) f
    (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with hfn
  -- ===== (0) Extract the weak gradient `(gx, gy)` from `MemW12loc f`. =====
  obtain ⟨_hLp, gx, gy, ⟨hwgx, hwgy⟩, hmgx, hmgy⟩ := hW12
  have hLpgx : MemLpLocOn gx 2 Set.univ := hmgx
  have hLpgy : MemLpLocOn gy 2 Set.univ := hmgy
  have hfloc : MeasureTheory.LocallyIntegrable f := hfcont.locallyIntegrable
  -- `L²_loc ⟹ L¹_loc ⟹ LocallyIntegrable`.
  have memLpLoc_to_loc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      MeasureTheory.LocallyIntegrable g := by
    intro g hg
    rw [← locallyIntegrableOn_univ, locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    have : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict k) :=
      ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    have hmem1 : MeasureTheory.MemLp g 1 (MeasureTheory.volume.restrict k) :=
      (hg k (Set.subset_univ _) hk).mono_exponent (by norm_num)
    exact MeasureTheory.memLp_one_iff_integrable.mp hmem1
  have hgxLI : MeasureTheory.LocallyIntegrable gx := memLpLoc_to_loc hLpgx
  have hgyLI : MeasureTheory.LocallyIntegrable gy := memLpLoc_to_loc hLpgy
  have hgxloc : MeasureTheory.LocallyIntegrableOn gx Set.univ :=
    locallyIntegrableOn_univ.mpr hgxLI
  have hgyloc : MeasureTheory.LocallyIntegrableOn gy Set.univ :=
    locallyIntegrableOn_univ.mpr hgyLI
  -- ===== (1) Smoothness / compact support of the mollifier. =====
  have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (φ n).contDiff_normed (n := ⊤)
  have hρsupp : ∀ n, HasCompactSupport (ρ n) := fun n => (φ n).hasCompactSupport_normed
  -- ===== (2) The two directional derivatives of `fn n` and of `f`. =====
  -- A1: `(fderiv (fn n) z) 1 = ρ n ⋆ gx z`, `(fderiv (fn n) z) I = ρ n ⋆ gy z` (every `z`).
  have hA1x : ∀ n z, (fderiv ℝ (fn n) z) (1 : ℂ)
      = MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
          MeasureTheory.volume z := fun n z =>
    fderiv_convolution_normed_apply_eq hwgx hfloc hgxLI (hρsm n) (hρsupp n) z
  have hA1y : ∀ n z, (fderiv ℝ (fn n) z) Complex.I
      = MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ)
          MeasureTheory.volume z := fun n z =>
    fderiv_convolution_normed_apply_eq hwgy hfloc hgyLI (hρsm n) (hρsupp n) z
  -- a.e.: `(fderiv f z) 1 = gx z`, `(fderiv f z) I = gy z`.
  have haex : ∀ᵐ z, (fderiv ℝ f z) (1 : ℂ) = gx z :=
    fderiv_ae_eq_weakDirDeriv hwgx hgxloc hdiff (Or.inl rfl) hfloc
  have haey : ∀ᵐ z, (fderiv ℝ f z) Complex.I = gy z :=
    fderiv_ae_eq_weakDirDeriv hwgy hgyloc hdiff (Or.inr rfl) hfloc
  -- ===== (4) Truncate the partials to a global `L²` function on `ball 0 (R+1)`. =====
  set gxR : ℂ → ℂ := (Metric.ball (0 : ℂ) (R + 1)).indicator gx with hgxR
  set gyR : ℂ → ℂ := (Metric.ball (0 : ℂ) (R + 1)).indicator gy with hgyR
  have hmemLp_trunc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      MeasureTheory.MemLp ((Metric.ball (0 : ℂ) (R + 1)).indicator g) 2
        MeasureTheory.volume := by
    intro g hg
    rw [MeasureTheory.memLp_indicator_iff_restrict measurableSet_ball]
    have hcb : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict
        (Metric.closedBall (0 : ℂ) (R + 1))) :=
      hg (Metric.closedBall (0 : ℂ) (R + 1)) (Set.subset_univ _)
        (isCompact_closedBall _ _)
    exact hcb.mono_measure (MeasureTheory.Measure.restrict_mono
      Metric.ball_subset_closedBall le_rfl)
  have hgxR_memLp : MeasureTheory.MemLp gxR 2 MeasureTheory.volume := hmemLp_trunc hLpgx
  have hgyR_memLp : MeasureTheory.MemLp gyR 2 MeasureTheory.volume := hmemLp_trunc hLpgy
  -- ===== The two scalar `L²` errors and their convergence (A2). =====
  set Ex : ℕ → ℝ≥0∞ := fun n => eLpNorm
    (MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
      - gxR) 2 MeasureTheory.volume with hEx
  set Ey : ℕ → ℝ≥0∞ := fun n => eLpNorm
    (MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
      - gyR) 2 MeasureTheory.volume with hEy
  have hExto : Filter.Tendsto Ex Filter.atTop (nhds 0) :=
    eLpNorm_convolution_normed_sub_tendsto_zero hgxR_memLp φ hφrout
  have hEyto : Filter.Tendsto Ey Filter.atTop (nhds 0) :=
    eLpNorm_convolution_normed_sub_tendsto_zero hgyR_memLp φ hφrout
  -- The dominating sequence `D n := 2 * (Ex n ^ 2 + Ey n ^ 2) → 0`.
  set D : ℕ → ℝ≥0∞ := fun n => 2 * (Ex n ^ 2 + Ey n ^ 2) with hD
  have hDto : Filter.Tendsto D Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun n => Ex n ^ 2 + Ey n ^ 2) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n => Ex n ^ 2) Filter.atTop (nhds 0) := by
        have := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp hExto
        simpa using! this
      have h2 : Filter.Tendsto (fun n => Ey n ^ 2) Filter.atTop (nhds 0) := by
        have := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp hEyto
        simpa using! this
      simpa using h1.add h2
    have hconst : Filter.Tendsto (fun n => (2 : ℝ≥0∞) * (Ex n ^ 2 + Ey n ^ 2))
        Filter.atTop (nhds ((2 : ℝ≥0∞) * 0)) :=
      ENNReal.Tendsto.const_mul hsq (Or.inr (ENNReal.ofNat_ne_top))
    simpa using hconst
  -- ===== (3)+(5)+(6) The eventual pointwise+integral domination. =====
  -- For `(φ n).rOut ≤ 1`, on a.e. `z ∈ ball 0 R`, the squared energy is `≤` the integrand
  -- of `D n`; integrating over `ball 0 R` and extending to the whole space gives the bound.
  have hev_rout : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 1 := by
    have := hφrout.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [this] with n hn using hn
  have hdom : ∀ᶠ n in Filter.atTop,
      (∫⁻ z in Metric.ball (0 : ℂ) R,
        (‖fderiv ℝ (fn n) z - fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2) ≤ D n := by
    filter_upwards [hev_rout] with n hrout1
    -- (5) On `ball 0 R`, the mollified partial = mollified truncation.
    have hconv_eq : ∀ {g : ℂ → ℂ}, ∀ z ∈ Metric.ball (0 : ℂ) R,
        MeasureTheory.convolution (ρ n) g (ContinuousLinearMap.lsmul ℝ ℝ)
            MeasureTheory.volume z
          = MeasureTheory.convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 1)).indicator g)
            (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume z := by
      intro g z hz
      rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      simp only
      by_cases ht : ρ n t = 0
      · simp only [ht, map_zero, zero_apply]
      · -- `ρ n t ≠ 0 ⟹ t ∈ support (ρ n) = ball 0 rOut`, so `‖t‖ < rOut ≤ 1`.
        have htsupp : t ∈ Function.support (ρ n) := ht
        rw [hρ, (φ n).support_normed_eq] at htsupp
        rw [Metric.mem_ball, dist_zero_right] at htsupp
        have hzlt : ‖z‖ < R := by
          rw [Metric.mem_ball, dist_zero_right] at hz; exact hz
        have hztmem : z - t ∈ Metric.ball (0 : ℂ) (R + 1) := by
          rw [Metric.mem_ball, dist_zero_right]
          calc ‖z - t‖ ≤ ‖z‖ + ‖t‖ := norm_sub_le _ _
            _ < R + 1 := by
              have : ‖t‖ < 1 := lt_of_lt_of_le htsupp hrout1
              linarith
        rw [Set.indicator_of_mem hztmem]
    -- (3) Operator-norm bound: `‖T‖₊^2 ≤ 2*(‖T 1‖₊^2 + ‖T I‖₊^2)` for a.e. `z ∈ ball R`.
    have hball_sub : Metric.ball (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) (R + 1) :=
      Metric.ball_subset_ball (by linarith)
    have hptbd : ∀ᵐ z, z ∈ Metric.ball (0 : ℂ) R →
        (‖fderiv ℝ (fn n) z - fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2 ≤
        2 * ((‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2
            + (‖MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z - gyR z‖₊ : ℝ≥0∞) ^ 2) := by
      filter_upwards [haex, haey] with z hzx hzy hzball
      set T := fderiv ℝ (fn n) z - fderiv ℝ f z with hT
      -- Identify the two basis components of `T`.
      have hTx : T (1 : ℂ) = MeasureTheory.convolution (ρ n) gxR
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume z - gxR z := by
        rw [hT, sub_apply, hA1x n z, hzx, hconv_eq z hzball,
          hgxR, Set.indicator_of_mem (hball_sub hzball)]
      have hTy : T Complex.I = MeasureTheory.convolution (ρ n) gyR
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume z - gyR z := by
        rw [hT, sub_apply, hA1y n z, hzy, hconv_eq z hzball,
          hgyR, Set.indicator_of_mem (hball_sub hzball)]
      -- `‖T‖ ≤ ‖T 1‖ + ‖T I‖`.
      have hopn : ‖T‖ ≤ ‖T (1 : ℂ)‖ + ‖T Complex.I‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
        have hTw : T w = w.re • T (1 : ℂ) + w.im • T Complex.I := by
          have hdecomp : w = w.re • (1 : ℂ) + w.im • Complex.I := by
            rw [Complex.real_smul, Complex.real_smul, mul_one]
            exact (Complex.re_add_im w).symm
          conv_lhs => rw [hdecomp]
          simp only [map_add, map_smul]
        calc ‖T w‖ = ‖w.re • T (1 : ℂ) + w.im • T Complex.I‖ := by rw [hTw]
          _ ≤ ‖w.re • T (1 : ℂ)‖ + ‖w.im • T Complex.I‖ := norm_add_le _ _
          _ ≤ ‖(w.re : ℝ)‖ * ‖T (1 : ℂ)‖ + ‖(w.im : ℝ)‖ * ‖T Complex.I‖ := by
              gcongr <;> exact norm_smul_le _ _
          _ = |w.re| * ‖T (1 : ℂ)‖ + |w.im| * ‖T Complex.I‖ := by
              rw [Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ ‖w‖ * ‖T (1 : ℂ)‖ + ‖w‖ * ‖T Complex.I‖ := by
              gcongr <;> [exact Complex.abs_re_le_norm w; exact Complex.abs_im_le_norm w]
          _ = (‖T (1 : ℂ)‖ + ‖T Complex.I‖) * ‖w‖ := by ring
      -- Transfer to `ℝ≥0`, square, and bound `(a+b)^2 ≤ 2(a^2+b^2)` in `ℝ≥0∞`.
      have hnn : ‖T‖₊ ≤ ‖T (1 : ℂ)‖₊ + ‖T Complex.I‖₊ := by
        rw [← NNReal.coe_le_coe]; push_cast; exact hopn
      have hle1 : (‖T‖₊ : ℝ≥0∞) ≤ (‖T (1 : ℂ)‖₊ : ℝ≥0∞) + (‖T Complex.I‖₊ : ℝ≥0∞) := by
        calc (‖T‖₊ : ℝ≥0∞) ≤ ((‖T (1 : ℂ)‖₊ + ‖T Complex.I‖₊ : ℝ≥0) : ℝ≥0∞) :=
              ENNReal.coe_le_coe.mpr hnn
          _ = (‖T (1 : ℂ)‖₊ : ℝ≥0∞) + (‖T Complex.I‖₊ : ℝ≥0∞) := by push_cast; ring
      calc (‖T‖₊ : ℝ≥0∞) ^ 2
          ≤ ((‖T (1 : ℂ)‖₊ : ℝ≥0∞) + (‖T Complex.I‖₊ : ℝ≥0∞)) ^ 2 := by gcongr
        _ ≤ 2 * ((‖T (1 : ℂ)‖₊ : ℝ≥0∞) ^ 2 + (‖T Complex.I‖₊ : ℝ≥0∞) ^ 2) := by
            have hkey := ENNReal.rpow_add_le_mul_rpow_add_rpow
              (‖T (1 : ℂ)‖₊ : ℝ≥0∞) (‖T Complex.I‖₊ : ℝ≥0∞) (by norm_num : (1 : ℝ) ≤ 2)
            have htwo : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
            rw [htwo] at hkey
            rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_natCast (‖T (1 : ℂ)‖₊ : ℝ≥0∞) 2,
              ← ENNReal.rpow_natCast (‖T Complex.I‖₊ : ℝ≥0∞) 2]
            push_cast
            exact hkey
        _ = 2 * ((‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2
              + (‖MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z - gyR z‖₊ : ℝ≥0∞) ^ 2) := by rw [hTx, hTy]
    -- Integrate over `ball 0 R` and bound by the full-space `eLpNorm`s.
    have hint_bd : (∫⁻ z in Metric.ball (0 : ℂ) R,
          (‖fderiv ℝ (fn n) z - fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2)
        ≤ ∫⁻ z in Metric.ball (0 : ℂ) R,
          2 * ((‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2
            + (‖MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z - gyR z‖₊ : ℝ≥0∞) ^ 2) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      rw [MeasureTheory.ae_restrict_iff' measurableSet_ball]
      filter_upwards [hptbd] with z hz using hz
    -- Compute the RHS as `D n` via `(eLpNorm · 2)^2 = ∫⁻ ‖·‖ₑ^2`.
    have heLpSq : ∀ (h : ℂ → ℂ), (eLpNorm h 2 MeasureTheory.volume) ^ 2
        = ∫⁻ z, (‖h z‖₊ : ℝ≥0∞) ^ 2 := by
      intro h
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num]
      have hlint_eq : (∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ)) = ∫⁻ z, (‖h z‖₊ : ℝ≥0∞) ^ 2 := by
        refine lintegral_congr (fun z => ?_)
        rw [enorm_eq_nnnorm, ← ENNReal.rpow_natCast (‖h z‖₊ : ℝ≥0∞) 2]
        norm_num
      rw [hlint_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
      norm_num
    -- Local integrability of the truncated partials (for convolution continuity).
    have hgxR_LI : MeasureTheory.LocallyIntegrable gxR :=
      hgxR_memLp.locallyIntegrable (by norm_num)
    have hgyR_LI : MeasureTheory.LocallyIntegrable gyR :=
      hgyR_memLp.locallyIntegrable (by norm_num)
    -- The two convolutions are continuous (`ρ n` smooth, compact support).
    have hconvx_cont : Continuous (MeasureTheory.convolution (ρ n) gxR
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) :=
      HasCompactSupport.continuous_convolution_left _ (hρsupp n)
        (hρsm n).continuous hgxR_LI
    -- AEMeasurability of the `x`-integrand `‖conv - gxR‖₊²`.
    have hmeasx : AEMeasurable (fun z =>
        (‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
            MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2) MeasureTheory.volume :=
      ((hconvx_cont.aestronglyMeasurable.sub
          hgxR_memLp.aestronglyMeasurable).aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2
    calc (∫⁻ z in Metric.ball (0 : ℂ) R,
          (‖fderiv ℝ (fn n) z - fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2)
        ≤ ∫⁻ z in Metric.ball (0 : ℂ) R,
            2 * ((‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
                  MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2
              + (‖MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ)
                  MeasureTheory.volume z - gyR z‖₊ : ℝ≥0∞) ^ 2) := hint_bd
      _ ≤ ∫⁻ z,
            2 * ((‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
                  MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2
              + (‖MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ)
                  MeasureTheory.volume z - gyR z‖₊ : ℝ≥0∞) ^ 2) :=
            MeasureTheory.setLIntegral_le_lintegral _ _
      _ = 2 * ((∫⁻ z, (‖MeasureTheory.convolution (ρ n) gxR (ContinuousLinearMap.lsmul ℝ ℝ)
                  MeasureTheory.volume z - gxR z‖₊ : ℝ≥0∞) ^ 2)
              + ∫⁻ z, (‖MeasureTheory.convolution (ρ n) gyR (ContinuousLinearMap.lsmul ℝ ℝ)
                  MeasureTheory.volume z - gyR z‖₊ : ℝ≥0∞) ^ 2) := by
            rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
              MeasureTheory.lintegral_add_left' hmeasx]
      _ = D n := by
            rw [hD, hEx, hEy]
            simp only [heLpSq, Pi.sub_apply]
  -- ===== Squeeze: `0 ≤ (·) ≤ D n` eventually, both bounds `→ 0`. =====
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hDto
    (Filter.Eventually.of_forall (fun n => zero_le)) hdom

/-- **(A: mollified-gradient `L²` energy decay on a ball.)** `IsQCAnalytic` wrapper of
`mollified_fderiv_ball_energy_tendsto_zero_of_memW12loc`. -/
theorem mollified_fderiv_ball_energy_tendsto_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (R : ℝ) (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφrout : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫⁻ z in Metric.ball (0 : ℂ) R,
        (‖fderiv ℝ (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
            (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) z
          - fderiv ℝ f z‖₊ : ℝ≥0∞) ^ 2)
      Filter.atTop (nhds 0) :=
  mollified_fderiv_ball_energy_tendsto_zero_of_memW12loc hf.1.1.continuous
    (IsQCAnalytic.ae_differentiableAt hf) hf.2.1 R φ hφrout

end NoWanderingDomains
