/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Geometric

/-!
# Quasiconformal calculus: composition

A geometric quasiconformal map is closed under composition: if `f` is geometrically
`Kf`-quasiconformal and `g` is geometrically `Kg`-quasiconformal, then `f ∘ g` is geometrically
`(Kf · Kg)`-quasiconformal. The modulus distortion bound composes multiplicatively,
`M((f∘g)(Q)) ≤ Kf · M(g(Q)) ≤ Kf · Kg · M(Q)`, realised through the image quadrilateral `g ∘ Q`
(`Quadrilateral.map`), whose connecting family is exactly `Q.imageCurveFamily g`.
-/

open Complex MeasureTheory
open scoped ENNReal Topology Real

namespace NoWanderingDomains

namespace Quadrilateral

/-- The image of a quadrilateral under a homeomorphism `g`, as a quadrilateral: its
parametrization is `g ∘ Q.toFun`, which is continuous and injective on the unit square. Its
sides and image region are the `g`-images of those of `Q`, and its connecting family is exactly
`Q.imageCurveFamily g`. -/
def map (Q : Quadrilateral) {g : ℂ → ℂ} (hg : IsHomeomorph g) : Quadrilateral where
  toFun := g ∘ Q.toFun
  continuous_toFun := hg.continuous.comp Q.continuous_toFun
  injOn_unitSquare := fun _ hx _ hy h => Q.injOn_unitSquare hx hy (hg.injective h)

@[simp] theorem map_toFun (Q : Quadrilateral) {g : ℂ → ℂ} (hg : IsHomeomorph g) :
    (Q.map hg).toFun = g ∘ Q.toFun := rfl

/-- The left side of `g ∘ Q` is the `g`-image of the left side of `Q`. -/
theorem map_leftSide (Q : Quadrilateral) {g : ℂ → ℂ} (hg : IsHomeomorph g) :
    (Q.map hg).leftSide = g '' Q.leftSide := by
  simp only [leftSide, map_toFun, Set.image_comp]

/-- The right side of `g ∘ Q` is the `g`-image of the right side of `Q`. -/
theorem map_rightSide (Q : Quadrilateral) {g : ℂ → ℂ} (hg : IsHomeomorph g) :
    (Q.map hg).rightSide = g '' Q.rightSide := by
  simp only [rightSide, map_toFun, Set.image_comp]

/-- The image region of `g ∘ Q` is the `g`-image of the image region of `Q`. -/
theorem map_image (Q : Quadrilateral) {g : ℂ → ℂ} (hg : IsHomeomorph g) :
    (Q.map hg).image = g '' Q.image := by
  simp only [image, map_toFun, Set.image_comp]

/-- The connecting family of the image quadrilateral `g ∘ Q` is exactly the image connecting
family of `Q` under `g`. -/
theorem map_curveFamily (Q : Quadrilateral) {g : ℂ → ℂ} (hg : IsHomeomorph g) :
    (Q.map hg).curveFamily = Q.imageCurveFamily g := by
  ext δ
  simp only [curveFamily, imageCurveFamily, Q.map_leftSide hg, Q.map_rightSide hg,
    Q.map_image hg, Set.mem_ofPred_eq]

/-- The image connecting family of `Q` under `f ∘ g` equals that of the image quadrilateral
`g ∘ Q` under `f`. -/
theorem imageCurveFamily_comp (Q : Quadrilateral) {f g : ℂ → ℂ} (hg : IsHomeomorph g) :
    Q.imageCurveFamily (f ∘ g) = (Q.map hg).imageCurveFamily f := by
  ext δ
  simp only [imageCurveFamily, Q.map_leftSide hg, Q.map_rightSide hg, Q.map_image hg,
    Set.image_comp, Set.mem_ofPred_eq]

end Quadrilateral

/-- **Sense-preservation is closed under composition.** The composite of two topologically
sense-preserving homeomorphisms is again sense-preserving. The homeomorphism part is
`IsHomeomorph.comp`. For the winding clause, the increment of a continuous logarithm of a closed
nonvanishing loop is invariant under homotopies through closed nonvanishing loops: a jointly
continuous family of such loops admits a jointly continuous family of lifts, whose endpoint
increment is `2πi` times a continuous `ℤ`-valued function of the parameter, hence constant. Two
consequences follow. First, every round image circle `θ ↦ f (w₀ + R e^{iθ}) − f w₀` winds `+1`
about `f w₀` for every centre `w₀` and radius `R > 0`, by homotoping centre and radius to a pair
supplied by the hypothesis on `f`. Second, the image loop `θ ↦ f (g z₀ + β(θ)) − f (g z₀)`, where
`β` is the small `g`-image circle about `g z₀` (a `+1` loop about `0` from the hypothesis on `g`),
is homotopic in the logarithm to the round circle `θ ↦ f (g z₀ + e^{iθ}) − f (g z₀)`, so it too
winds `+1`. A periodic global continuous logarithm of the resulting loop is assembled from an
interval lift via `AddCircle.liftIco`. -/
theorem SensePreserving.comp {f g : ℂ → ℂ} (hf : SensePreserving f) (hg : SensePreserving g) :
    SensePreserving (f ∘ g) := by
  refine ⟨hf.1.comp hg.1, ?_⟩
  have hWD : ∀ (L₁ L₂ : ℝ → ℂ), Continuous L₁ → Continuous L₂ →
      (∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), Complex.exp (L₁ t) = Complex.exp (L₂ t)) →
      L₁ (2 * Real.pi) - L₁ 0 = L₂ (2 * Real.pi) - L₂ 0 := by
    intro L₁ L₂ hL₁ hL₂ hexp
    have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have h2pi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    set d : ℝ → ℂ := fun t => L₁ t - L₂ t with hd
    have hdcont : Continuous d := hL₁.sub hL₂
    have hdexp : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), Complex.exp (d t) = 1 := by
      intro t ht
      simp only [hd, Complex.exp_sub, hexp t ht, div_self (Complex.exp_ne_zero _)]
    have hdK : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ∃ K : ℤ, d t = (K : ℂ) * (2 * Real.pi * Complex.I) := fun t ht =>
      (Complex.exp_eq_one_iff).mp (hdexp t ht)
    classical
    set wfun : ℝ → ℤ :=
      fun t => if h : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) then (hdK t h).choose else 0 with hwf
    have hwf_spec : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        d t = ((wfun t : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      intro t ht; simp only [hwf, dif_pos ht]; exact (hdK t ht).choose_spec
    have hwf_cont : ContinuousOn (fun t => ((wfun t : ℤ) : ℂ)) (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
      have heq : Set.EqOn (fun t => ((wfun t : ℤ) : ℂ))
          (fun t => d t / (2 * Real.pi * Complex.I)) (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
        intro t ht
        simp only
        rw [hwf_spec t ht, mul_div_assoc, div_self h2pi_ne, mul_one]
      exact ContinuousOn.congr (hdcont.continuousOn.div_const _) heq
    have hwf_int_cont : ContinuousOn wfun (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
      rw [continuousOn_iff_continuous_domRestrict] at hwf_cont ⊢
      have hemb : Topology.IsClosedEmbedding (fun n : ℤ => (n : ℂ)) :=
        Complex.isClosedEmbedding_intCast
      exact hemb.isEmbedding.continuous_iff.mpr hwf_cont
    have hconst : wfun 0 = wfun (2 * Real.pi) :=
      isPreconnected_Icc.constant hwf_int_cont ⟨le_refl _, hpi⟩ ⟨hpi, le_refl _⟩
    have hdd : d (2 * Real.pi) = d 0 := by
      rw [hwf_spec (2 * Real.pi) ⟨hpi, le_refl _⟩, hwf_spec 0 ⟨le_refl _, hpi⟩, hconst]
    simp only [hd] at hdd
    linear_combination hdd
  have HI : ∀ (U : ℝ → ℝ → ℂ),
      ContinuousOn (Function.uncurry U) (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)) →
      (∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), U s t ≠ 0) →
      (∀ s ∈ Set.Icc (0:ℝ) 1, U s 0 = U s (2 * Real.pi)) →
      ∀ (L0 L1 : ℝ → ℂ), Continuous L0 → Continuous L1 →
        (∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), Complex.exp (L0 t) = U 0 t) →
        (∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), Complex.exp (L1 t) = U 1 t) →
        L0 (2 * Real.pi) - L0 0 = L1 (2 * Real.pi) - L1 0 := by
    intro U hUc hUne hUclosed L0 L1 hL0c hL1c hL0e hL1e
    have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have h2pi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    -- parametrized lift
    obtain ⟨Lp, hLpc, hLpe⟩ := continuous_log_lift_param_of_continuous_ne_zero
      (by norm_num : (0:ℝ) ≤ 1) hpi U hUc hUne
    -- increment as a function of s
    set inc : ℝ → ℂ := fun s => Lp s (2 * Real.pi) - Lp s 0 with hinc
    have hinc_cont : Continuous inc := by
      refine Continuous.sub ?_ ?_
      · exact (hLpc.comp (continuous_id.prodMk continuous_const))
      · exact (hLpc.comp (continuous_id.prodMk continuous_const))
    -- inc s = 2πi K(s)
    have hincK : ∀ s ∈ Set.Icc (0:ℝ) 1, ∃ K : ℤ, inc s = (K : ℂ) * (2 * Real.pi * Complex.I) := by
      intro s hs
      have hexp_eq : Complex.exp (Lp s (2 * Real.pi)) = Complex.exp (Lp s 0) := by
        rw [hLpe s hs (2*Real.pi) ⟨hpi, le_refl _⟩, hLpe s hs 0 ⟨le_refl _, hpi⟩,
            ← hUclosed s hs]
      have : Complex.exp (inc s) = 1 := by
        rw [hinc]; simp only [Complex.exp_sub, hexp_eq, div_self (Complex.exp_ne_zero _)]
      exact (Complex.exp_eq_one_iff).mp this
    classical
    set Kf : ℝ → ℤ :=
      fun s => if h : s ∈ Set.Icc (0:ℝ) 1 then (hincK s h).choose else 0 with hKf
    have hKf_spec : ∀ s ∈ Set.Icc (0:ℝ) 1,
        inc s = ((Kf s : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      intro s hs; simp only [hKf, dif_pos hs]; exact (hincK s hs).choose_spec
    have hKf_cont : ContinuousOn (fun s => ((Kf s : ℤ) : ℂ)) (Set.Icc (0:ℝ) 1) := by
      have heq : Set.EqOn (fun s => ((Kf s : ℤ) : ℂ))
          (fun s => inc s / (2 * Real.pi * Complex.I)) (Set.Icc (0:ℝ) 1) := by
        intro s hs; simp only
        rw [hKf_spec s hs, mul_div_assoc, div_self h2pi_ne, mul_one]
      exact ContinuousOn.congr (hinc_cont.continuousOn.div_const _) heq
    have hKf_int_cont : ContinuousOn Kf (Set.Icc (0:ℝ) 1) := by
      rw [continuousOn_iff_continuous_domRestrict] at hKf_cont ⊢
      have hemb : Topology.IsClosedEmbedding (fun n : ℤ => (n : ℂ)) :=
        Complex.isClosedEmbedding_intCast
      exact hemb.isEmbedding.continuous_iff.mpr hKf_cont
    have hKconst : Kf 0 = Kf 1 :=
      isPreconnected_Icc.constant hKf_int_cont ⟨le_refl _, zero_le_one⟩ ⟨zero_le_one, le_refl _⟩
    have hinc_eq : inc 0 = inc 1 := by
      rw [hKf_spec 0 ⟨le_refl _, zero_le_one⟩, hKf_spec 1 ⟨zero_le_one, le_refl _⟩, hKconst]
    -- relate L0 increment to inc 0 and L1 increment to inc 1
    have hL0_inc : L0 (2 * Real.pi) - L0 0 = inc 0 := by
      rw [hinc]; simp only
      refine hWD L0 (fun t => Lp 0 t) hL0c (hLpc.comp (continuous_const.prodMk continuous_id)) ?_
      intro t ht
      rw [hL0e t ht, hLpe 0 ⟨le_refl _, zero_le_one⟩ t ht]
    have hL1_inc : L1 (2 * Real.pi) - L1 0 = inc 1 := by
      rw [hinc]; simp only
      refine hWD L1 (fun t => Lp 1 t) hL1c (hLpc.comp (continuous_const.prodMk continuous_id)) ?_
      intro t ht
      rw [hL1e t ht, hLpe 1 ⟨zero_le_one, le_refl _⟩ t ht]
    rw [hL0_inc, hL1_inc, hinc_eq]
  have hDf : ∀ (w₀ : ℂ) (R : ℝ), 0 < R → ∀ (Lc : ℝ → ℂ), Continuous Lc →
      (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi),
        Complex.exp (Lc θ) = f (w₀ + (R : ℂ) * Complex.exp ((θ:ℂ) * Complex.I)) - f w₀) →
      Lc (2 * Real.pi) - Lc 0 = 2 * (Real.pi : ℂ) * Complex.I := by
    have hfc : Continuous f := hf.1.continuous
    have hfinj : Function.Injective f := hf.1.injective
    -- pick a good center c and radius ρ₀ from hf.2
    obtain ⟨c, hc⟩ := hf.2.exists
    have hpos : ∀ᶠ r in 𝓝[>] (0:ℝ), (0:ℝ) < r := by
      rw [eventually_nhdsWithin_iff]; filter_upwards with r hr using hr
    obtain ⟨ρ₀, hρ₀_pos, Lρ, hLρc, hLρe, hLρincr⟩ := (hpos.and hc).exists
    intro w₀ R hR Lc hLcc hLce
    -- circle loop family parameterized by (center, radius)
    -- helper: exp(iθ) nonzero norm 1
    have hexp_ne : ∀ θ : ℝ, Complex.exp ((θ:ℂ) * Complex.I) ≠ 0 := fun θ => Complex.exp_ne_zero _
    -- generic round circle loop nonvanishing for positive radius:
    have hcircle_ne : ∀ (a : ℂ) (ρ : ℝ), 0 < ρ → ∀ θ : ℝ,
        f (a + (ρ:ℂ) * Complex.exp ((θ:ℂ)*Complex.I)) - f a ≠ 0 := by
      intro a ρ hρ θ h
      have heq : f (a + (ρ:ℂ) * Complex.exp ((θ:ℂ)*Complex.I)) = f a := by
        rw [sub_eq_zero] at h; exact h
      have := hfinj heq
      have hz : (ρ:ℂ) * Complex.exp ((θ:ℂ)*Complex.I) = 0 := left_eq_add.mp this.symm
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact (ne_of_gt hρ) (by exact_mod_cast h1)
      · exact hexp_ne θ h2
    -- closedness of round circle loop in θ
    have hcircle_closed : ∀ (a : ℂ) (ρ : ℝ),
        f (a + (ρ:ℂ) * Complex.exp (((0:ℝ):ℂ)*Complex.I)) - f a
        = f (a + (ρ:ℂ) * Complex.exp (((2*Real.pi:ℝ):ℂ)*Complex.I)) - f a := by
      intro a ρ
      congr 3
      rw [show (((2 * Real.pi : ℝ) : ℂ)) * Complex.I
            = (((0:ℝ):ℂ)) * Complex.I + ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
            push_cast; ring]
      rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    -- the homotopy U_A: center (1-s)c + s w₀, radius (1-s)ρ₀ + s R
    set cen : ℝ → ℂ := fun s => (1 - (s:ℂ)) * c + (s:ℂ) * w₀ with hcen
    set rad : ℝ → ℝ := fun s => (1 - s) * ρ₀ + s * R with hrad
    have hrad_pos : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 < rad s := by
      intro s hs; obtain ⟨h0, h1⟩ := hs
      rcases lt_or_eq_of_le h1 with hlt | heq
      · have : 0 < (1 - s) * ρ₀ := mul_pos (by linarith) hρ₀_pos
        simp only [hrad]; nlinarith [mul_nonneg h0 hR.le]
      · subst heq; simp only [hrad]; simpa using hR
    set U : ℝ → ℝ → ℂ :=
      fun s θ => f (cen s + ((rad s : ℝ):ℂ) * Complex.exp ((θ:ℂ)*Complex.I)) - f (cen s) with hU
    have hUc : ContinuousOn (Function.uncurry U)
        (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)) := by
      apply Continuous.continuousOn
      simp only [hU]
      refine Continuous.sub ?_ ?_
      · refine hfc.comp ?_
        refine Continuous.add ?_ ?_
        · refine Continuous.add ?_ ?_
          · exact (continuous_const.sub
              (Complex.continuous_ofReal.comp continuous_fst)).mul continuous_const
          · exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_const
        · refine Continuous.mul ?_ (Complex.continuous_exp.comp ?_)
          · refine Complex.continuous_ofReal.comp ?_
            simp only [hrad]
            exact ((continuous_const.sub continuous_fst).mul continuous_const).add
              (continuous_fst.mul continuous_const)
          · exact (Complex.continuous_ofReal.comp continuous_snd).mul continuous_const
      · refine hfc.comp ?_
        refine Continuous.add ?_ ?_
        · exact (continuous_const.sub
            (Complex.continuous_ofReal.comp continuous_fst)).mul continuous_const
        · exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_const
    have hUne : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), U s θ ≠ 0 := by
      intro s hs θ _; exact hcircle_ne (cen s) (rad s) (hrad_pos s hs) θ
    have hUclosed : ∀ s ∈ Set.Icc (0:ℝ) 1, U s 0 = U s (2 * Real.pi) := by
      intro s _; exact hcircle_closed (cen s) (rad s)
    -- U 0 = (c, ρ₀) circle ; U 1 = (w₀, R) circle
    have hU0 : ∀ θ, U 0 θ = f (c + (ρ₀:ℂ) * Complex.exp ((θ:ℂ)*Complex.I)) - f c := by
      intro θ; simp only [hU, hcen, hrad]; norm_num
    have hU1 : ∀ θ, U 1 θ = f (w₀ + (R:ℂ) * Complex.exp ((θ:ℂ)*Complex.I)) - f w₀ := by
      intro θ; simp only [hU, hcen, hrad]; norm_num
    -- apply HI with L0 := Lρ, L1 := Lc
    have hmain := HI U hUc hUne hUclosed Lρ Lc hLρc hLcc
      (fun θ _ => by rw [hU0 θ]; exact hLρe θ)
      (fun θ hθ => by rw [hU1 θ]; exact hLce θ hθ)
    rw [hmain] at hLρincr
    exact hLρincr
  have hGlobal : ∀ (γ : ℝ → ℂ), Continuous γ → Function.Periodic γ (2 * Real.pi) →
      ∀ (Lb : ℝ → ℂ), Continuous Lb →
      (∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), Complex.exp (Lb t) = γ t) →
      ∃ L : ℝ → ℂ, Continuous L ∧ (∀ θ, Complex.exp (L θ) = γ θ)
        ∧ L (2 * Real.pi) - L 0 = Lb (2 * Real.pi) - Lb 0 := by
    intro γ hγc hγper Lb hLbc hLbe
    have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
    have h2pic : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt h2pi)
    have : Fact ((0:ℝ) < 2 * Real.pi) := ⟨h2pi⟩
    have hγne : ∀ θ, γ θ ≠ 0 := by
      intro θ
      -- γ θ = exp(...) somewhere via periodicity; but simpler: from hLbe on [0,2π] we get nonzero
      -- reduce θ to Ico, but easier: γ never 0 since it's exp on [0,2π] and periodic
      have hb := AddCircle.eq_coe_Ico (𝕜 := ℝ) (p := 2 * Real.pi) (↑θ)
      obtain ⟨b, hb_mem, hb_coe⟩ := hb
      have hθb : (↑θ : AddCircle (2*Real.pi)) = ↑b := hb_coe.symm
      rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at hθb
      obtain ⟨n, hn⟩ := hθb
      rw [zsmul_eq_mul] at hn
      have hθeq : θ = b + (-n : ℤ) • (2 * Real.pi) := by
        rw [zsmul_eq_mul]; push_cast; linarith [hn]
      rw [hθeq, (hγper.zsmul (-n)) b, ← hLbe b ⟨hb_mem.1, le_of_lt hb_mem.2⟩]
      exact Complex.exp_ne_zero _
    set V : ℂ := Lb (2 * Real.pi) - Lb 0 with hV
    have hexpV : Complex.exp V = 1 := by
      have h0 : Complex.exp (Lb 0) = γ 0 := hLbe 0 ⟨le_refl _, le_of_lt h2pi⟩
      have h2 : Complex.exp (Lb (2*Real.pi)) = γ (2*Real.pi) :=
        hLbe (2*Real.pi) ⟨le_of_lt h2pi, le_refl _⟩
      have hper0 : γ (2*Real.pi) = γ 0 := by have := hγper 0; rwa [zero_add] at this
      rw [hV, Complex.exp_sub, h0, h2, hper0, div_self (hγne 0)]
    set P : ℝ → ℂ := fun t => Lb t - ((t : ℂ) / (2 * Real.pi)) * V with hP
    have hPc : Continuous P :=
      hLbc.sub ((Complex.continuous_ofReal.div_const _).mul continuous_const)
    have hPend : P 0 = P (0 + 2 * Real.pi) := by
      simp only [hP, zero_add]
      rw [hV]; push_cast; field_simp; ring
    set Pt : AddCircle (2 * Real.pi) → ℂ := AddCircle.liftIco (2 * Real.pi) 0 P with hPt
    have hPtc : Continuous Pt := by
      refine AddCircle.liftIco_continuous hPend ?_
      rw [zero_add]; exact hPc.continuousOn
    set L : ℝ → ℂ := fun θ => Pt (↑θ) + ((θ : ℂ) / (2 * Real.pi)) * V with hL
    have hLc : Continuous L :=
      (hPtc.comp continuous_quotient_mk').add
        ((Complex.continuous_ofReal.div_const _).mul continuous_const)
    have hLexp_Ico : ∀ θ ∈ Set.Ico (0:ℝ) (2 * Real.pi), Complex.exp (L θ) = γ θ := by
      intro θ hθ
      have hcoe : Pt (↑θ) = P θ := by
        rw [hPt]
        have := AddCircle.liftIco_coe_apply (p := 2 * Real.pi) (a := 0) (f := P) (x := θ)
          (by rw [zero_add]; exact hθ)
        exact this
      rw [hL]; simp only
      rw [hcoe, hP]; simp only
      rw [show Lb θ - (↑θ / (2 * ↑Real.pi)) * V + (↑θ / (2 * ↑Real.pi)) * V = Lb θ by ring]
      exact hLbe θ ⟨hθ.1, le_of_lt hθ.2⟩
    have hexpLper : Function.Periodic (fun θ => Complex.exp (L θ)) (2 * Real.pi) := by
      intro θ
      simp only [hL]
      rw [AddCircle.coe_add_period]
      rw [Complex.exp_add, Complex.exp_add]
      congr 1
      rw [show ((θ + 2 * Real.pi : ℝ) : ℂ) / (2 * Real.pi) * V
          = (↑θ / (2 * ↑Real.pi)) * V + V by field_simp; push_cast; ring]
      rw [Complex.exp_add, hexpV, mul_one]
    have hLexp : ∀ θ, Complex.exp (L θ) = γ θ := by
      intro θ
      obtain ⟨b, hb_mem, hb_coe⟩ := AddCircle.eq_coe_Ico (𝕜 := ℝ) (p := 2 * Real.pi) (↑θ)
      have hθb : (↑θ : AddCircle (2*Real.pi)) = ↑b := hb_coe.symm
      rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at hθb
      obtain ⟨n, hn⟩ := hθb
      rw [zsmul_eq_mul] at hn
      have hθeq : θ = b + (-n : ℤ) • (2 * Real.pi) := by rw [zsmul_eq_mul]; push_cast; linarith [hn]
      rw [hθeq]
      have h1 := (hexpLper.zsmul (-n)) b
      have h2 := (hγper.zsmul (-n)) b
      try simp only at h1
      rw [h1, h2]
      exact hLexp_Ico b ⟨hb_mem.1, hb_mem.2⟩
    refine ⟨L, hLc, hLexp, ?_⟩
    have hPt2pi : Pt (↑(2 * Real.pi : ℝ)) = Pt (↑(0:ℝ)) := by
      have : ((2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) = ((0:ℝ) : AddCircle (2 * Real.pi)) := by
        have := AddCircle.coe_add_period (2 * Real.pi) (0:ℝ)
        rwa [zero_add] at this
      rw [this]
    simp only [hL]
    rw [hPt2pi]
    have hz : ((0:ℝ) : ℂ) / (2 * Real.pi) * V = 0 := by simp
    have h2pic' : (2 * (Real.pi:ℂ)) ≠ 0 := by
      rw [show (2 * (Real.pi:ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]; exact h2pic
    have hone : ((2 * Real.pi : ℝ) : ℂ) / (2 * Real.pi) * V = V := by
      rw [show ((2 * Real.pi : ℝ) : ℂ) = (2 * Real.pi : ℂ) by push_cast; ring]
      rw [div_self h2pic', one_mul]
    rw [hz, hone]; ring
  have hfc : Continuous f := hf.1.continuous
  have hfinj : Function.Injective f := hf.1.injective
  have hgc : Continuous g := hg.1.continuous
  have hginj : Function.Injective g := hg.1.injective
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hexp_ne : ∀ θ : ℝ, Complex.exp ((θ:ℂ) * Complex.I) ≠ 0 := fun θ => Complex.exp_ne_zero _
  have hpos : ∀ᶠ r in 𝓝[>] (0:ℝ), (0:ℝ) < r := by
    rw [eventually_nhdsWithin_iff]; filter_upwards with r hr using hr
  filter_upwards [hg.2] with z₀ hz₀
  filter_upwards [hpos, hz₀] with r hr hr_data
  obtain ⟨Lg, hLgc, hLge, hLgincr⟩ := hr_data
  set w₀ : ℂ := g z₀ with hw₀
  set rC : ℂ := (r : ℂ) with hrC
  -- target loop γ_F (all θ), continuous, periodic, nonvanishing
  set γF : ℝ → ℂ := fun θ => f (g (z₀ + rC * Complex.exp ((θ:ℂ)*Complex.I))) - f (g z₀) with hγF
  -- exp(Lg θ) = g(z₀ + r e^{iθ}) - g z₀
  have hβ : ∀ θ, Complex.exp (Lg θ) = g (z₀ + rC * Complex.exp ((θ:ℂ)*Complex.I)) - g z₀ := hLge
  -- γF θ = f (w₀ + exp(Lg θ)) - f w₀
  have hγF_eq : ∀ θ, γF θ = f (w₀ + Complex.exp (Lg θ)) - f w₀ := by
    intro θ; simp only [hγF, hw₀]
    rw [hβ θ]; ring_nf
  have hγFc : Continuous γF := by
    simp only [hγF]
    refine Continuous.sub ?_ continuous_const
    refine hfc.comp (hgc.comp ?_)
    exact continuous_const.add (continuous_const.mul (Complex.continuous_exp.comp (by fun_prop)))
  have hγFperiod : Function.Periodic γF (2 * Real.pi) := by
    intro θ
    simp only [hγF]
    congr 3
    rw [show ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
          = ((θ:ℝ):ℂ) * Complex.I + ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
          push_cast; ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hrC_ne : rC ≠ 0 := by rw [hrC]; exact_mod_cast (ne_of_gt hr)
  have hγFne : ∀ θ, γF θ ≠ 0 := by
    intro θ h
    simp only [hγF] at h
    rw [sub_eq_zero] at h
    have h1 := hginj (hfinj h)
    have h2 : rC * Complex.exp ((θ:ℂ)*Complex.I) = 0 := left_eq_add.mp h1.symm
    rcases mul_eq_zero.mp h2 with h3 | h4
    · exact hrC_ne h3
    · exact hexp_ne θ h4
  -- the homotopy U from γF (s=0) to the unit circle at w₀ (s=1)
  set expo : ℝ → ℝ → ℂ := fun s θ => (1 - (s:ℂ)) * Lg θ + (s:ℂ) * ((θ:ℂ) * Complex.I) with hexpo
  set U : ℝ → ℝ → ℂ := fun s θ => f (w₀ + Complex.exp (expo s θ)) - f w₀ with hU
  have hexpoc : Continuous (Function.uncurry expo) := by
    simp only [hexpo]
    refine Continuous.add ?_ ?_
    · exact (continuous_const.sub (Complex.continuous_ofReal.comp continuous_fst)).mul
        (hLgc.comp continuous_snd)
    · refine (Complex.continuous_ofReal.comp continuous_fst).mul ?_
      exact (Complex.continuous_ofReal.comp continuous_snd).mul continuous_const
  have hUc : ContinuousOn (Function.uncurry U)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)) := by
    apply Continuous.continuousOn
    simp only [hU]
    refine Continuous.sub ?_ continuous_const
    refine hfc.comp ?_
    refine continuous_const.add (Complex.continuous_exp.comp ?_)
    exact hexpoc
  -- exp(expo s 0) and exp(expo s 2π) agree (increment 2πi)
  have hexpo_closed : ∀ s, Complex.exp (expo s (2 * Real.pi)) = Complex.exp (expo s 0) := by
    intro s
    simp only [hexpo]
    rw [Complex.exp_add, Complex.exp_add]
    have hLgexp : Complex.exp ((1 - (s:ℂ)) * Lg (2 * Real.pi))
        = Complex.exp ((1 - (s:ℂ)) * Lg 0)
          * Complex.exp ((1 - (s:ℂ)) * (2 * (Real.pi:ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      have : Lg (2 * Real.pi) = Lg 0 + (2 * (Real.pi:ℂ) * Complex.I) := by
        linear_combination hLgincr
      rw [this]; ring
    have hcircexp : Complex.exp ((s:ℂ) * (((2*Real.pi:ℝ):ℂ) * Complex.I))
        = Complex.exp ((s:ℂ) * (((0:ℝ):ℂ) * Complex.I))
          * Complex.exp ((s:ℂ) * (2 * (Real.pi:ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast; ring
    rw [hLgexp, hcircexp]
    rw [show (1 - (s:ℂ)) * (2 * (Real.pi:ℂ) * Complex.I)
          = (2 * (Real.pi:ℂ) * Complex.I) - (s:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) by ring]
    rw [Complex.exp_sub]
    have h2pi1 : Complex.exp (2 * (Real.pi:ℂ) * Complex.I) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I 1; push_cast at this
      rw [show (2 * (Real.pi:ℂ) * Complex.I) = (1:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) by ring]
      exact this
    rw [h2pi1]
    field_simp
  have hUne : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), U s θ ≠ 0 := by
    intro s _ θ _ h
    simp only [hU] at h
    rw [sub_eq_zero] at h
    have hh := hfinj h
    exact Complex.exp_ne_zero _ (left_eq_add.mp hh.symm)
  have hUclosed : ∀ s ∈ Set.Icc (0:ℝ) 1, U s 0 = U s (2 * Real.pi) := by
    intro s _
    simp only [hU]
    rw [hexpo_closed s]
  -- U 0 = γF
  have hU0 : ∀ θ, U 0 θ = γF θ := by
    intro θ
    simp only [hU, hexpo]
    rw [hγF_eq θ]
    congr 2
    push_cast; ring_nf
  -- U 1 = unit circle at w₀
  have hU1 : ∀ θ, U 1 θ = f (w₀ + (1:ℂ) * Complex.exp ((θ:ℂ)*Complex.I)) - f w₀ := by
    intro θ
    simp only [hU, hexpo]
    congr 2
    push_cast; ring_nf
  -- Build an Icc-lift of γF
  obtain ⟨LbF, hLbFc, hLbFe⟩ := continuous_log_lift_of_continuous_ne_zero_Icc
    (le_of_lt h2pi) γF hγFc.continuousOn (fun θ _ => hγFne θ)
  -- Build an Icc-lift of the unit circle at w₀
  set circ : ℝ → ℂ := fun θ => f (w₀ + (1:ℂ) * Complex.exp ((θ:ℂ)*Complex.I)) - f w₀ with hcirc
  have hcircc : Continuous circ := by
    simp only [hcirc]
    refine Continuous.sub ?_ continuous_const
    refine hfc.comp (continuous_const.add ?_)
    exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  have hcircne : ∀ θ, circ θ ≠ 0 := by
    intro θ h
    simp only [hcirc] at h
    rw [sub_eq_zero] at h
    have hh := hfinj h
    have h2 : (1:ℂ) * Complex.exp ((θ:ℂ)*Complex.I) = 0 := left_eq_add.mp hh.symm
    rw [one_mul] at h2
    exact hexp_ne θ h2
  obtain ⟨Lcirc, hLcircc, hLcirce⟩ := continuous_log_lift_of_continuous_ne_zero_Icc
    (le_of_lt h2pi) circ hcircc.continuousOn (fun θ _ => hcircne θ)
  -- HI: LbF increment = Lcirc increment
  have hHI := HI U hUc hUne hUclosed LbF Lcirc hLbFc hLcircc
    (fun θ hθ => by rw [hU0 θ]; exact hLbFe θ hθ)
    (fun θ hθ => by rw [hU1 θ]; exact hLcirce θ hθ)
  -- hDf: Lcirc increment = 2πi (round circle radius 1 at w₀)
  have hcirc_incr : Lcirc (2 * Real.pi) - Lcirc 0 = 2 * (Real.pi:ℂ) * Complex.I := by
    refine hDf w₀ 1 one_pos Lcirc hLcircc ?_
    intro θ hθ
    rw [hLcirce θ hθ, hcirc]
    norm_num
  have hLbF_incr : LbF (2 * Real.pi) - LbF 0 = 2 * (Real.pi:ℂ) * Complex.I := by
    rw [hHI, hcirc_incr]
  -- Global lift of γF with increment 2πi
  obtain ⟨L, hLc, hLe, hLincr⟩ := hGlobal γF hγFc hγFperiod LbF hLbFc hLbFe
  refine ⟨L, hLc, ?_, ?_⟩
  · intro θ
    rw [hLe θ]
    simp only [hγF, Function.comp_apply, hrC]
  · rw [hLincr, hLbF_incr]

/-- **Geometric quasiconformality is closed under composition.** If `f` is geometrically
`Kf`-quasiconformal and `g` is geometrically `Kg`-quasiconformal, then `f ∘ g` is geometrically
`(Kf · Kg)`-quasiconformal. For every quadrilateral `Q`, the image connecting family of `f ∘ g`
is the image family of the quadrilateral `g ∘ Q` under `f`, so the modulus distortion chains:
`M((f∘g)(Q)) ≤ Kf · M(g(Q)) = Kf · M(Q.imageCurveFamily g) ≤ Kf · Kg · M(Q)`. -/
theorem IsQCGeometric.comp {f g : ℂ → ℂ} {Kf Kg : ℝ}
    (hf : IsQCGeometric f Kf) (hg : IsQCGeometric g Kg) :
    IsQCGeometric (f ∘ g) (Kf * Kg) := by
  obtain ⟨hKf, hspf, hmodf⟩ := hf
  obtain ⟨hKg, hspg, hmodg⟩ := hg
  have hgh : IsHomeomorph g := hspg.isHomeomorph
  refine ⟨?_, hspf.comp hspg, fun Q => ?_⟩
  · nlinarith [hKf, hKg, mul_nonneg (sub_nonneg.2 hKf) (sub_nonneg.2 hKg)]
  · have hmapmod : (Q.map hgh).modulus = curveModulus (Q.imageCurveFamily g) := by
      rw [Quadrilateral.modulus, Q.map_curveFamily hgh]
    rw [Quadrilateral.imageCurveFamily_comp Q hgh]
    calc curveModulus ((Q.map hgh).imageCurveFamily f)
        ≤ ENNReal.ofReal Kf * (Q.map hgh).modulus := hmodf (Q.map hgh)
      _ = ENNReal.ofReal Kf * curveModulus (Q.imageCurveFamily g) := by rw [hmapmod]
      _ ≤ ENNReal.ofReal Kf * (ENNReal.ofReal Kg * Q.modulus) := by gcongr; exact hmodg Q
      _ = ENNReal.ofReal (Kf * Kg) * Q.modulus := by
          rw [ENNReal.ofReal_mul (le_trans zero_le_one hKf), mul_assoc]

end NoWanderingDomains
