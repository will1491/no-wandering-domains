/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.Morrey.OscillationBound

/-!
# Lusin (N) for super-critical Sobolev functions on `ℂ`

For `p > 2` a continuous function `f : ℂ → ℂ` with weak gradient `(gx, gy) ∈ Lᵖ_loc`
is Hölder continuous of exponent `1 - 2/p` (Morrey) and maps null sets to null sets
(Lusin's condition (N)). The Lusin (N) property is derived here from the Morrey
oscillation bound `exists_morrey_oscillation_bound` via a Besicovitch covering and a
discrete Hölder inequality, followed by a mollification-free `ε → 0` limit.
-/

open MeasureTheory Complex Metric Set Function
open scoped ContDiff ENNReal NNReal Convolution Topology

namespace NoWanderingDomains

set_option maxHeartbeats 400000 in
-- This proof inlines the Besicovitch covering, the per-ball Morrey/volume estimate, a discrete
-- Hölder inequality and the final mollification-free `ε → 0` limit as nested `have`s; the resulting
-- elaboration needs the raised heartbeat budget.
theorem lusinN_image_null_of_weakGradient {p : ℝ} (hp : 2 < p) {f gx gy : ℂ → ℂ}
    (hf : Continuous f) (hgrad : HasWeakGradient gx gy f Set.univ)
    (hgx : MemLpLocOn gx (ENNReal.ofReal p) Set.univ)
    (hgy : MemLpLocOn gy (ENNReal.ofReal p) Set.univ)
    {E : Set ℂ} (hE : volume E = 0) :
    volume (f '' E) = 0 := by
  classical
  -- Basic numerology for `p`.
  have hp0 : (0 : ℝ) < p := by linarith
  have hp_2p : (0 : ℝ) < 2 / p := by positivity
  have h2p_lt1 : 2 / p < 1 := by rw [div_lt_one hp0]; linarith
  have hθpos : (0 : ℝ) < 1 - 2 / p := by linarith
  -- The Morrey oscillation bound.
  obtain ⟨C, hC0, hMor⟩ := exists_morrey_oscillation_bound hp hf hgrad hgx hgy
  -- The nonnegative gradient-energy density and its `ℝ≥0∞` lift.
  set g : ℂ → ℝ := fun z => ‖gx z‖ ^ p + ‖gy z‖ ^ p with hgdef
  have hg_nonneg : ∀ z, 0 ≤ g z := fun z => by rw [hgdef]; positivity
  set G : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (g z) with hGdef
  have hp_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Local integrability and a.e.-measurability of `gx`, `gy`, `g`, `G`.
  have hgxloc : LocallyIntegrable gx (volume : Measure ℂ) := by
    rw [locallyIntegrable_iff]; intro K hK
    have hmemlp : MemLp gx (ENNReal.ofReal p) (volume.restrict K) := hgx K (Set.subset_univ _) hK
    have : IsFiniteMeasure (volume.restrict K) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top
    exact hmemlp.integrable hp_one_le
  have hgyloc : LocallyIntegrable gy (volume : Measure ℂ) := by
    rw [locallyIntegrable_iff]; intro K hK
    have hmemlp : MemLp gy (ENNReal.ofReal p) (volume.restrict K) := hgy K (Set.subset_univ _) hK
    have : IsFiniteMeasure (volume.restrict K) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top
    exact hmemlp.integrable hp_one_le
  have hgx_aesm : AEStronglyMeasurable gx (volume : Measure ℂ) := hgxloc.aestronglyMeasurable
  have hgy_aesm : AEStronglyMeasurable gy (volume : Measure ℂ) := hgyloc.aestronglyMeasurable
  have hg_aesm : AEStronglyMeasurable g (volume : Measure ℂ) := by
    rw [hgdef]
    exact ((hgx_aesm.norm.aemeasurable.pow_const p).add
      (hgy_aesm.norm.aemeasurable.pow_const p)).aestronglyMeasurable
  have hG_aemeas : AEMeasurable G (volume : Measure ℂ) := by
    rw [hGdef]; exact hg_aesm.aemeasurable.ennreal_ofReal
  -- Reduce to null image of `E ∩ ball 0 R` for each natural `R`.
  suffices hkey : ∀ R : ℕ, volume (f '' (E ∩ ball (0:ℂ) (R:ℝ))) = 0 by
    have hcover : f '' E = ⋃ R : ℕ, f '' (E ∩ ball (0:ℂ) (R:ℝ)) := by
      rw [← Set.image_iUnion]; congr 1
      rw [← Set.inter_iUnion, Metric.iUnion_ball_nat, Set.inter_univ]
    rw [hcover]
    refine le_antisymm ?_ (zero_le)
    calc volume (⋃ R : ℕ, f '' (E ∩ ball (0:ℂ) (R:ℝ)))
        ≤ ∑' R : ℕ, volume (f '' (E ∩ ball (0:ℂ) (R:ℝ))) := measure_iUnion_le _
      _ = 0 := by simp [hkey]
  -- Fix `R`. Write `S := E ∩ ball 0 R`; it is null and contained in `ball 0 R`.
  intro R
  set S : Set ℂ := E ∩ ball (0:ℂ) (R:ℝ) with hSdef
  have hSsub : S ⊆ ball (0:ℂ) (R:ℝ) := Set.inter_subset_right
  have hSnull : volume S = 0 := by
    rw [hSdef]; exact measure_mono_null Set.inter_subset_left hE
  -- The energy density is finite on the compact `closedBall 0 (R+1)`.
  have hball_sub : ball (0:ℂ) (R:ℝ) ⊆ ball (0:ℂ) ((R:ℝ) + 1) :=
    Metric.ball_subset_ball (by linarith)
  have hball_cb : ball (0:ℂ) ((R:ℝ) + 1) ⊆ closedBall (0:ℂ) ((R:ℝ) + 1) :=
    Metric.ball_subset_closedBall
  -- `g` is integrable on `closedBall 0 (R+1)`; its `ℝ≥0∞`-lift has finite lintegral there.
  have hgInt_cb : IntegrableOn g (closedBall (0:ℂ) ((R:ℝ) + 1)) volume := by
    have hcb : IsCompact (closedBall (0:ℂ) ((R:ℝ) + 1)) := isCompact_closedBall _ _
    have hmx : MemLp gx (ENNReal.ofReal p) (volume.restrict (closedBall (0:ℂ) ((R:ℝ)+1))) :=
      hgx _ (Set.subset_univ _) hcb
    have hmy : MemLp gy (ENNReal.ofReal p) (volume.restrict (closedBall (0:ℂ) ((R:ℝ)+1))) :=
      hgy _ (Set.subset_univ _) hcb
    have hp_ofReal_ne : ENNReal.ofReal p ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0
    have hxp : Integrable (fun z => ‖gx z‖ ^ p)
        (volume.restrict (closedBall (0:ℂ) ((R:ℝ)+1))) := by
      have := hmx.integrable_norm_rpow hp_ofReal_ne ENNReal.ofReal_ne_top
      simpa [ENNReal.toReal_ofReal hp0.le] using this
    have hyp : Integrable (fun z => ‖gy z‖ ^ p)
        (volume.restrict (closedBall (0:ℂ) ((R:ℝ)+1))) := by
      have := hmy.integrable_norm_rpow hp_ofReal_ne ENNReal.ofReal_ne_top
      simpa [ENNReal.toReal_ofReal hp0.le] using this
    rw [IntegrableOn, hgdef]; exact hxp.add hyp
  have hGlint_cb : ∫⁻ z in closedBall (0:ℂ) ((R:ℝ) + 1), G z ∂volume ≠ ⊤ := by
    rw [hGdef]
    have : ∫⁻ z in closedBall (0:ℂ) ((R:ℝ)+1), ENNReal.ofReal (g z) ∂volume
        = ENNReal.ofReal (∫ z in closedBall (0:ℂ) ((R:ℝ)+1), g z ∂volume) := by
      rw [ofReal_integral_eq_lintegral_ofReal hgInt_cb (ae_of_all _ hg_nonneg)]
    rw [this]; exact ENNReal.ofReal_ne_top
  -- The Hölder exponents `P = p/(p-2)` and `Q = p/2`.
  set P : ℝ := p / (p - 2) with hPdef
  set Q : ℝ := p / 2 with hQdef
  have hPpos : 0 < P := by rw [hPdef]; exact div_pos hp0 (by linarith)
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  have hPQ : P.HolderConjugate Q := by
    rw [hPdef, hQdef, Real.holderConjugate_iff]
    refine ⟨by rw [lt_div_iff₀ (by linarith)]; linarith, ?_⟩
    rw [inv_div, inv_div, div_add_div _ _ (by positivity) (by positivity),
      div_eq_one_iff_eq (by positivity)]; ring
  have hPinv : 1 / P = 1 - 2 / p := by
    rw [hPdef, one_div, inv_div]; field_simp
  have hQinv : 1 / Q = 2 / p := by rw [hQdef, one_div, inv_div]
  -- The dimensional multiplicity constant.
  set M : ℕ := 58 with hMdef
  -- The constant `K = ofReal(C² π)`, finite.
  set K : ℝ≥0∞ := ENNReal.ofReal (C ^ 2 * Real.pi) with hKdef
  have hK_ne_top : K ≠ ⊤ := by rw [hKdef]; exact ENNReal.ofReal_ne_top
  -- It suffices to bound `volume (f '' S)` by `K' * ε^(1-2/p)` for every `ε > 0`, `K'` fixed.
  -- We fix an open neighbourhood `U ⊇ S` with `volume U < 1` (energy budget `η = 1`), and let
  -- the Besicovitch slack `ε` tend to `0`.
  obtain ⟨U, hUopen, hSU, hUcb, hUmeas⟩ :
      ∃ U : Set ℂ, IsOpen U ∧ S ⊆ U ∧ U ⊆ ball (0:ℂ) ((R:ℝ)+1)
        ∧ volume U < 1 := by
    obtain ⟨V, hSV, hVopen, hVmeas⟩ :=
      Set.exists_isOpen_lt_of_lt S 1 (by rw [hSnull]; exact one_pos)
    refine ⟨V ∩ ball (0:ℂ) ((R:ℝ)+1), hVopen.inter Metric.isOpen_ball,
      Set.subset_inter hSV (hSsub.trans (Metric.ball_subset_ball (by linarith))),
      Set.inter_subset_right, lt_of_le_of_lt (measure_mono Set.inter_subset_left) hVmeas⟩
  -- `∫⁻_U G` is finite (since `U ⊆ closedBall 0 (R+1)`).
  have hGU_ne_top : ∫⁻ z in U, G z ≠ ⊤ := by
    refine ne_top_of_le_ne_top hGlint_cb ?_
    exact lintegral_mono_set (hUcb.trans hball_cb)
  -- The energy-budget constant `Kη := K * (M * ∫⁻_U G)^(2/p)`, which is finite.
  set Kη : ℝ≥0∞ := K * ((M : ℝ≥0∞) * (∫⁻ z in U, G z)) ^ (2 / p) with hKηdef
  have hKη_ne_top : Kη ≠ ⊤ := by
    rw [hKηdef]
    refine ENNReal.mul_ne_top hK_ne_top (ENNReal.rpow_ne_top_of_nonneg hp_2p.le ?_)
    exact ENNReal.mul_ne_top (by simp) hGU_ne_top
  -- The slack-parametrised bound.
  have hMainBound : ∀ ε : ℝ≥0∞, 0 < ε →
      volume (f '' S) ≤ Kη * (ε * (ENNReal.ofReal Real.pi)⁻¹) ^ (1 - 2 / p) := by
    intro ε hεpos
    -- A *bounded-overlap* cover of `S` by closed balls, with total measure `≤ ε`, all doubled
    -- balls inside `U`, and the doubled-ball energy controlled by the multiplicity constant `M`.
    -- Such a cover exists: the Besicovitch covering theorem refined to a single dyadic shell of
    -- comparable radii makes the doubled balls have multiplicity `≤ M = multiplicity ℂ`, which
    -- gives both the total-measure bound and the energy bound
    -- `∑ₓ ∫_{ball x 2rₓ} G ≤ M ∫_U G` via the comparable-radii Besicovitch packing inequality.
    obtain ⟨t, r, ht_count, htS, hr_pos, hScov, hball_in_U, htsum, hEnergy⟩ :
        ∃ (t : Set ℂ) (r : ℂ → ℝ), t.Countable ∧ t ⊆ S ∧ (∀ x ∈ t, 0 < r x) ∧
          (S ⊆ ⋃ x ∈ t, closedBall x (r x)) ∧ (∀ x ∈ t, ball x (2 * r x) ⊆ U) ∧
          (∑' x : t, volume (closedBall (x : ℂ) (r (x : ℂ))) ≤ volume S + ε) ∧
          (∑' x : t, (∫⁻ z in ball (x : ℂ) (2 * r (x : ℂ)), G z)
            ≤ (58 : ℝ≥0∞) * (∫⁻ z in U, G z)) := by
      classical
      -- Volume packing count.
      have packing_volume : ∀ (y : ℂ) (R₀ σ : ℝ), 0 < σ → 0 ≤ R₀ → ∀ (F : Finset ℂ),
          (∀ c ∈ F, dist c y ≤ R₀) →
          (∀ c ∈ F, ∀ d ∈ F, c ≠ d → σ ≤ dist c d) →
          (F.card : ℝ) * (σ/2)^2 ≤ (R₀ + σ/2)^2 := by
        intro y R₀ σ hσ hR F hnear hsep
        have hv0 : volume (ball (0:ℂ) 1) ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
        have hvt : volume (ball (0:ℂ) 1) ≠ ⊤ := measure_ball_lt_top.ne
        have hdisj : (F : Set ℂ).PairwiseDisjoint (fun c => ball c (σ/2)) := by
          intro a ha b hb hab
          exact ball_disjoint_ball (by linarith [hsep a ha b hb hab])
        have hsub : (⋃ c ∈ F, ball c (σ/2)) ⊆ ball y (R₀ + σ/2) := by
          intro z hz
          simp only [mem_iUnion] at hz
          obtain ⟨c, hc, hz⟩ := hz
          rw [mem_ball] at hz ⊢
          calc dist z y ≤ dist z c + dist c y := dist_triangle z c y
            _ < σ/2 + R₀ := by linarith [hnear c hc]
            _ = R₀ + σ/2 := by ring
        have hmono : volume (⋃ c ∈ F, ball c (σ/2)) ≤ volume (ball y (R₀ + σ/2)) :=
          measure_mono hsub
        have hsum : ∑ c ∈ F, volume (ball c (σ/2)) = volume (⋃ c ∈ F, ball c (σ/2)) :=
          (measure_biUnion_finset hdisj (fun c _ => measurableSet_ball)).symm
        have hv : ∀ c : ℂ,
            volume (ball c (σ/2)) = ENNReal.ofReal ((σ/2)^2) * volume (ball (0:ℂ) 1) := by
          intro c
          rw [Measure.addHaar_ball_of_pos volume c (by linarith : (0:ℝ) < σ/2)]
          congr 1; norm_num [Complex.finrank_real_complex]
        have hvR : volume (ball y (R₀ + σ/2))
            = ENNReal.ofReal ((R₀+σ/2)^2) * volume (ball (0:ℂ) 1) := by
          rw [Measure.addHaar_ball_of_pos volume y (by linarith : (0:ℝ) < R₀ + σ/2)]
          congr 1; norm_num [Complex.finrank_real_complex]
        rw [← hsum, hvR] at hmono
        simp only [hv, Finset.sum_const, nsmul_eq_mul] at hmono
        rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hv0 hvt] at hmono
        rw [← ENNReal.ofReal_natCast F.card, ← ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmono
        exact hmono
      -- Doubled-ball overlap bound.
      have overlap_bound : ∀ (g : ℂ → ℝ), LipschitzWith (1/8 : ℝ≥0) g →
          ∀ (y : ℂ), 0 < g y → ∀ (F : Finset ℂ), (∀ x ∈ F, 0 < g x) →
          (∀ x ∈ F, dist x y < 2 * g x) →
          (∀ x ∈ F, ∀ x' ∈ F, x ≠ x' → min (g x) (g x') ≤ dist x x') →
          F.card ≤ 58 := by
        intro g hgL y hgy F hgF hF hsep
        have hcomp : ∀ x ∈ F, g x < (4/3) * g y ∧ (4/5) * g y < g x := by
          intro x hx
          have hL := hgL.dist_le_mul x y
          rw [Real.dist_eq] at hL; push_cast at hL
          have h2 : dist x y < 2 * g x := hF x hx
          have hab := abs_le.mp hL
          exact ⟨by nlinarith [hab.1, hab.2, h2, hgF x hx, hgy],
                 by nlinarith [hab.1, hab.2, h2, hgF x hx, hgy]⟩
        set R₀ := (8/3) * g y with hRdef
        set σ := (4/5) * g y with hσdef
        have hσpos : 0 < σ := by rw [hσdef]; linarith
        have hRpos : 0 ≤ R₀ := by rw [hRdef]; linarith
        have hnear : ∀ c ∈ F, dist c y ≤ R₀ := by
          intro c hc
          have h2 := hF c hc
          have := (hcomp c hc).1
          rw [hRdef]; linarith
        have hsep' : ∀ c ∈ F, ∀ d ∈ F, c ≠ d → σ ≤ dist c d := by
          intro c hc d hd hcd
          have h := hsep c hc d hd hcd
          have hc1 := (hcomp c hc).2
          have hd1 := (hcomp d hd).2
          rw [hσdef]
          calc (4/5) * g y ≤ min (g c) (g d) := le_min hc1.le hd1.le
            _ ≤ dist c d := h
        have hpack := packing_volume y R₀ σ hσpos hRpos F hnear hsep'
        have hσ2 : (0:ℝ) < (σ/2)^2 := by positivity
        have hcard : (F.card : ℝ) ≤ (R₀ + σ/2)^2 / (σ/2)^2 := by
          rw [le_div_iff₀ hσ2]; exact hpack
        have hval : (R₀ + σ/2)^2 / (σ/2)^2 < 59 := by
          rw [hRdef, hσdef, div_lt_iff₀ (by positivity)]
          nlinarith [hgy, sq_nonneg (g y)]
        have hlt : (F.card : ℝ) < 59 := lt_of_le_of_lt hcard hval
        have : F.card < 59 := by exact_mod_cast hlt
        omega
      -- Maximal separated net.
      have exists_maximal_separated : ∀ (S₀ : Set ℂ) (g : ℂ → ℝ),
          ∃ t ⊆ S₀, (∀ x ∈ t, ∀ y ∈ t, x ≠ y → min (g x) (g y) ≤ dist x y) ∧
            (∀ s ∈ S₀, ∃ x ∈ t, dist s x < min (g s) (g x) ∨ s = x) := by
        intro S₀ g
        let P : Set (Set ℂ) :=
          {t | t ⊆ S₀ ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → min (g x) (g y) ≤ dist x y}
        have hchain : ∀ c ⊆ P, IsChain (· ⊆ ·) c → ∃ ub ∈ P, ∀ s ∈ c, s ⊆ ub := by
          intro c hc hchain
          rcases eq_empty_or_nonempty c with rfl | hne
          · exact ⟨∅, ⟨empty_subset _, by simp⟩, by simp⟩
          refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => subset_sUnion_of_mem hs⟩
          · intro x hx
            simp only [mem_sUnion] at hx
            obtain ⟨t, ht, hxt⟩ := hx
            exact (hc ht).1 hxt
          · intro x hx y hy hxy
            simp only [mem_sUnion] at hx hy
            obtain ⟨tx, htx, hxtx⟩ := hx
            obtain ⟨ty, hty, hyty⟩ := hy
            rcases hchain.total htx hty with h | h
            · exact (hc hty).2 x (h hxtx) y hyty hxy
            · exact (hc htx).2 x hxtx y (h hyty) hxy
        obtain ⟨m, hm⟩ := zorn_subset P hchain
        refine ⟨m, hm.1.1, hm.1.2, ?_⟩
        intro s hs
        by_contra hcon
        push Not at hcon
        have hsm : s ∉ m := fun h => (hcon s h).2 rfl
        have hP : m ∪ {s} ∈ P := by
          refine ⟨union_subset hm.1.1 (by simp [hs]), ?_⟩
          intro x hx y hy hxy
          simp only [mem_union, mem_singleton_iff] at hx hy
          obtain hx | hx := hx
          · obtain hy | hy := hy
            · exact hm.1.2 x hx y hy hxy
            · subst hy
              have h1 := (hcon x hx).1
              rw [dist_comm, min_comm]
              exact h1
          · subst hx
            obtain hy | hy := hy
            · exact (hcon y hy).1
            · subst hy; exact absurd rfl hxy
        have := hm.2 hP subset_union_left
        exact hsm (this (by simp))
      -- A min-separated net with positive gauge is countable.
      have net_countable : ∀ (t : Set ℂ) (g : ℂ → ℝ), (∀ x ∈ t, 0 < g x) →
          (∀ x ∈ t, ∀ y ∈ t, x ≠ y → min (g x) (g y) ≤ dist x y) →
          t.Countable := by
        intro t g hg hsep
        have hcover : t = ⋃ n : ℕ, {x ∈ t | 1 / (n+1 : ℝ) < g x} := by
          ext x
          simp only [mem_iUnion, mem_ofPred_eq]
          constructor
          · intro hx
            obtain ⟨n, hn⟩ := exists_nat_gt (1 / g x)
            refine ⟨n, hx, ?_⟩
            have hgx := hg x hx
            rw [div_lt_iff₀ hgx] at hn
            rw [div_lt_iff₀ (by positivity)]
            nlinarith [hn, hgx]
          · rintro ⟨n, hx, _⟩; exact hx
        rw [hcover]
        apply countable_iUnion
        intro n
        set δ := 1 / (n + 1 : ℝ) with hδ
        have hδpos : 0 < δ := by positivity
        apply Set.PairwiseDisjoint.countable_of_nonempty_interior
          (s := fun x => ball x (δ/2))
        · intro x hx y hy hxy
          simp only [Function.onFun]
          apply ball_disjoint_ball
          have h1 : δ ≤ min (g x) (g y) := le_min hx.2.le hy.2.le
          have h2 := hsep x hx.1 y hy.1 hxy
          linarith [le_trans h1 h2]
        · intro x _
          rw [interior_eq_iff_isOpen.mpr isOpen_ball]
          exact ⟨x, mem_ball_self (by positivity)⟩
      -- The pointwise indicator-sum bound.
      have indicator_tsum_le : ∀ (t : Set ℂ), t.Countable → ∀ (g : ℂ → ℝ),
          LipschitzWith (1/8 : ℝ≥0) g →
          (∀ x ∈ t, ∀ x' ∈ t, x ≠ x' → min (g x) (g x') ≤ dist x x') →
          ∀ (H : ℂ → ℝ≥0∞) (W : Set ℂ), (∀ x ∈ t, ball x (2 * g x) ⊆ W) →
          (∀ z ∈ W, 0 < g z) → (∀ x ∈ t, 0 < g x) → ∀ (y : ℂ),
          ∑' i : t, (ball (i:ℂ) (2 * g i)).indicator H y ≤ 58 * W.indicator H y := by
        intro t ht g hgL hsep H W hW hgposW hgpost y
        have : Countable ↥t := ht.to_subtype
        by_cases hyW : y ∈ W
        · rw [Set.indicator_of_mem hyW]
          have hgy : 0 < g y := hgposW y hyW
          set J : Set ℂ := {x | x ∈ t ∧ dist x y < 2 * g x} with hJdef
          have hJfin : J.Finite := by
            by_contra hinf
            rw [Set.not_finite] at hinf
            obtain ⟨F, hFJ, hFcard⟩ := hinf.exists_subset_card_eq 59
            have hFmem : ∀ x ∈ F, x ∈ J := fun x hx => hFJ hx
            have h1 : ∀ x ∈ F, dist x y < 2 * g x := fun x hx => (hFmem x hx).2
            have h2 : ∀ x ∈ F, ∀ x' ∈ F, x ≠ x' → min (g x) (g x') ≤ dist x x' :=
              fun x hx x' hx' hxx' => hsep x (hFmem x hx).1 x' (hFmem x' hx').1 hxx'
            have hgF : ∀ x ∈ F, 0 < g x := fun x hx => hgpost x (hFmem x hx).1
            have := overlap_bound g hgL y hgy F hgF h1 h2
            omega
          have hJcard : hJfin.toFinset.card ≤ 58 := by
            apply overlap_bound g hgL y hgy
            · intro x hx
              rw [Set.Finite.mem_toFinset] at hx
              exact hgpost x hx.1
            · intro x hx
              rw [Set.Finite.mem_toFinset] at hx
              exact hx.2
            · intro x hx x' hx' hxx'
              rw [Set.Finite.mem_toFinset] at hx hx'
              exact hsep x hx.1 x' hx'.1 hxx'
          have hterm : ∀ i : t, (ball (i:ℂ) (2 * g i)).indicator H y =
              J.indicator (fun _ => H y) (i:ℂ) := by
            intro i
            rw [Set.indicator_apply, Set.indicator_apply]
            have hiff : (y ∈ ball (i:ℂ) (2 * g i)) ↔ (i:ℂ) ∈ J := by
              rw [mem_ball, hJdef]; simp only [mem_ofPred_eq, i.2, true_and]; rw [dist_comm]
            by_cases h : (i:ℂ) ∈ J
            · rw [if_pos (hiff.mpr h), if_pos h]
            · rw [if_neg (fun hy => h (hiff.mp hy)), if_neg h]
          simp_rw [hterm]
          set fI : ↥t → ℝ≥0∞ := fun i => J.indicator (fun _ => H y) (i:ℂ) with hfdef
          have hf : ∀ i, fI i ≤ H y := by
            intro i; rw [hfdef]; dsimp only; rw [Set.indicator_apply]
            split_ifs with h
            · exact le_refl _
            · exact zero_le
          have hsupp0 : ∀ i : ↥t, (i:ℂ) ∉ J → fI i = 0 := by
            intro i hi; rw [hfdef]; dsimp only; exact Set.indicator_of_notMem hi _
          have hSfin : {i : ↥t | (i:ℂ) ∈ J}.Finite :=
            Set.Finite.preimage (Subtype.val_injective.injOn) hJfin
          set sF : Finset ↥t := hSfin.toFinset with hsdef
          have hsupp : ∀ i ∉ sF, fI i = 0 := by
            intro i hi
            apply hsupp0
            intro hJmem
            exact hi (by rw [hsdef, Set.Finite.mem_toFinset]; exact hJmem)
          have hscard : sF.card ≤ 58 := by
            have hinj : Set.InjOn (Subtype.val : ↥t → ℂ) sF := Subtype.val_injective.injOn
            have himg : sF.image (Subtype.val) ⊆ hJfin.toFinset := by
              intro x hx
              simp only [Finset.mem_image, hsdef, Set.Finite.mem_toFinset, mem_ofPred_eq] at hx
              obtain ⟨i, hi, rfl⟩ := hx
              rw [Set.Finite.mem_toFinset]; exact hi
            calc sF.card = (sF.image Subtype.val).card := (Finset.card_image_of_injOn hinj).symm
              _ ≤ hJfin.toFinset.card := Finset.card_le_card himg
              _ ≤ 58 := hJcard
          rw [tsum_eq_sum hsupp]
          calc ∑ i ∈ sF, fI i ≤ ∑ i ∈ sF, H y := Finset.sum_le_sum (fun i _ => hf i)
            _ = sF.card • H y := Finset.sum_const _
            _ = (sF.card : ℝ≥0∞) * H y := nsmul_eq_mul _ _
            _ ≤ 58 * H y := by gcongr; exact_mod_cast hscard
        · have hz : ∀ i : t, (ball (i:ℂ) (2 * g i)).indicator H y = 0 := by
            intro i
            rw [Set.indicator_apply]
            split_ifs with hy
            · exact absurd (hW i i.2 hy) hyW
            · rfl
          simp only [hz, tsum_zero]; exact zero_le
      -- The Lipschitz gauge `g0 V x = min (1/100) ((1/8)·dist(x,Vᶜ))`.
      let g0 : Set ℂ → ℂ → ℝ := fun V x => min (1/100 : ℝ) ((1/8) * infDist x Vᶜ)
      have g0_lip : ∀ (V : Set ℂ), LipschitzWith (1/8 : ℝ≥0) (g0 V) := by
        intro V
        have h1 : LipschitzWith 1 (fun x => infDist x Vᶜ) := lipschitz_infDist_pt Vᶜ
        have h2 : LipschitzWith (1/8 : ℝ≥0) (fun x => (1/8:ℝ) * infDist x Vᶜ) := by
          apply LipschitzWith.of_dist_le_mul
          intro x y
          rw [Real.dist_eq, ← mul_sub, abs_mul]
          have hfd := h1.dist_le_mul x y
          rw [Real.dist_eq] at hfd; push_cast at hfd ⊢
          rw [abs_of_pos (by norm_num : (0:ℝ) < 1/8)]
          nlinarith [abs_nonneg (infDist x Vᶜ - infDist y Vᶜ), hfd]
        exact h2.const_min _
      have g0_pos : ∀ (V : Set ℂ), IsOpen V → ∀ (x : ℂ), x ∈ V → (Vᶜ).Nonempty →
          0 < g0 V x := by
        intro V hVopen x hx hVne
        apply lt_min (by norm_num)
        have hcl : IsClosed (Vᶜ) := isClosed_compl_iff.mpr hVopen
        have : 0 < infDist x Vᶜ := (hcl.notMem_iff_infDist_pos hVne).mp (by simp [hx])
        positivity
      have g0_ball_subset : ∀ (V : Set ℂ) (x : ℂ), ball x (2 * g0 V x) ⊆ V := by
        intro V x w hw
        rw [mem_ball] at hw
        by_contra hwV
        have hwc : w ∈ Vᶜ := hwV
        have hle : infDist x Vᶜ ≤ dist x w := infDist_le_dist_of_mem hwc
        rw [dist_comm] at hle
        have hg0x : g0 V x = min (1/100 : ℝ) ((1/8) * infDist x Vᶜ) := rfl
        have hbound : 2 * g0 V x ≤ (1/4) * infDist x Vᶜ := by
          rw [hg0x]
          have := min_le_right (1/100 : ℝ) ((1/8)*infDist x Vᶜ)
          nlinarith [this, infDist_nonneg (x := x) (s := Vᶜ)]
        have hipos : 0 ≤ infDist x Vᶜ := infDist_nonneg
        linarith
      -- The main body.
      set β : ℝ≥0∞ := min (ε / 58) 1 with hβdef
      have hβ0 : β ≠ 0 := by
        rw [hβdef]
        have : (0:ℝ≥0∞) < min (ε/58) 1 :=
          lt_min (ENNReal.div_pos hεpos.ne' (by norm_num)) (by norm_num)
        exact this.ne'
      obtain ⟨V0, hV0S, hV0open, hV0vol⟩ := Set.exists_isOpen_le_add S volume hβ0
      set V : Set ℂ := V0 ∩ U with hVdef
      have hVopen : IsOpen V := hV0open.inter hUopen
      have hVmeas : MeasurableSet V := hVopen.measurableSet
      have hSV : S ⊆ V := fun x hx => ⟨hV0S hx, hSU hx⟩
      have hVU : V ⊆ U := inter_subset_right
      have hVvol : volume V ≤ volume S + β := le_trans (measure_mono inter_subset_left) hV0vol
      have hVvol_lt : volume V < ⊤ := by
        refine lt_of_le_of_lt hVvol ?_
        rw [hSnull, zero_add]
        exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hVne : (Vᶜ).Nonempty := by
        rw [Set.nonempty_compl]; intro h; rw [h] at hVvol_lt; simp at hVvol_lt
      set g : ℂ → ℝ := g0 V with hgdef0
      have hgL : LipschitzWith (1/8 : ℝ≥0) g := g0_lip V
      have hgposV : ∀ x ∈ V, 0 < g x := fun x hx => g0_pos V hVopen x hx hVne
      have hball : ∀ x, ball x (2 * g x) ⊆ V := fun x => g0_ball_subset V x
      obtain ⟨t, htS, hsep, hcov⟩ := exists_maximal_separated S g
      have htV : t ⊆ V := fun x hx => hSV (htS hx)
      have hgpost : ∀ x ∈ t, 0 < g x := fun x hx => hgposV x (htV hx)
      have htcount : t.Countable := net_countable t g hgpost hsep
      have : Countable ↥t := htcount.to_subtype
      refine ⟨t, g, htcount, htS, hgpost, ?_, ?_, ?_, ?_⟩
      · intro s hs
        obtain ⟨x, hxt, hx⟩ := hcov s hs
        rw [mem_iUnion₂]
        refine ⟨x, hxt, ?_⟩
        rw [mem_closedBall]
        rcases hx with hlt | heq
        · exact le_of_lt (lt_of_lt_of_le hlt (min_le_right _ _))
        · rw [heq, dist_self]; exact (hgpost x hxt).le
      · intro x hx
        exact (hball x).trans hVU
      · have hstep : ∑' x : t, volume (closedBall (x:ℂ) (g x)) ≤ 58 * volume V := by
          calc ∑' x : t, volume (closedBall (x:ℂ) (g x))
              ≤ ∑' x : t, volume (ball (x:ℂ) (2 * g x)) := by
                apply ENNReal.tsum_le_tsum
                intro x
                apply measure_mono
                apply closedBall_subset_ball
                have := hgpost x.1 x.2; linarith
            _ = ∑' x : t, ∫⁻ z in ball (x:ℂ) (2 * g x), (1 : ℝ≥0∞) := by
                congr 1; ext x; rw [setLIntegral_one]
            _ = ∫⁻ z, ∑' x : t, (ball (x:ℂ) (2 * g x)).indicator (fun _ => (1:ℝ≥0∞)) z := by
                rw [lintegral_tsum (fun i => (aemeasurable_const).indicator measurableSet_ball)]
                congr 1; ext x; rw [← lintegral_indicator measurableSet_ball]
            _ ≤ ∫⁻ z, 58 * V.indicator (fun _ => (1:ℝ≥0∞)) z := by
                apply lintegral_mono
                intro z
                exact indicator_tsum_le t htcount g hgL hsep (fun _ => (1:ℝ≥0∞)) V
                  (fun x hx => hball x) hgposV hgpost z
            _ = 58 * volume V := by
                rw [lintegral_const_mul' 58 _ (by norm_num),
                    lintegral_indicator hVmeas, setLIntegral_one]
        calc ∑' x : t, volume (closedBall (x:ℂ) (g x)) ≤ 58 * volume V := hstep
          _ ≤ 58 * (volume S + β) := by gcongr
          _ = 58 * (β) := by rw [hSnull, zero_add]
          _ ≤ 58 * (ε / 58) := by gcongr; exact min_le_left _ _
          _ ≤ ε := by
              rw [mul_comm, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
          _ ≤ volume S + ε := le_add_self
      · calc ∑' x : t, ∫⁻ z in ball (x:ℂ) (2 * g x), G z
            = ∫⁻ z, ∑' x : t, (ball (x:ℂ) (2 * g x)).indicator G z := by
              rw [lintegral_tsum (fun i => hG_aemeas.indicator measurableSet_ball)]
              congr 1; ext x; rw [← lintegral_indicator measurableSet_ball]
          _ ≤ ∫⁻ z, 58 * V.indicator G z := by
              apply lintegral_mono
              intro z
              exact indicator_tsum_le t htcount g hgL hsep G V
                (fun x hx => hball x) hgposV hgpost z
          _ = 58 * ∫⁻ z in V, G z := by
              rw [lintegral_const_mul' 58 _ (by norm_num),
                  lintegral_indicator hVmeas]
          _ ≤ 58 * ∫⁻ z in U, G z := by gcongr
    have : Countable t := ht_count.to_subtype
    -- The per-ball volume bound, packaged with `a x := (ofReal (r x))^2` and
    -- `e x := ∫⁻_{ball x (2 r x)} G`.
    set a : t → ℝ≥0∞ := fun x => (ENNReal.ofReal (r (x : ℂ))) ^ 2 with hadef
    set e : t → ℝ≥0∞ := fun x => ∫⁻ z in ball (x : ℂ) (2 * r (x : ℂ)), G z
      with hedef
    -- `S ⊆ ⋃ closed balls`, so the image is covered by the per-ball images.
    have himg_cov : volume (f '' S)
        ≤ ∑' x : t, volume (f '' (closedBall (x : ℂ) (r (x : ℂ)))) := by
      have h1 : f '' S ⊆ ⋃ x ∈ t, f '' (closedBall x (r x)) := by
        intro w hw
        obtain ⟨z, hz, rfl⟩ := hw
        obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.1 (hScov hz)
        exact Set.mem_iUnion₂.2 ⟨x, hxt, ⟨z, hzx, rfl⟩⟩
      calc volume (f '' S) ≤ volume (⋃ x ∈ t, f '' (closedBall x (r x))) := measure_mono h1
        _ ≤ ∑' x : t, volume (f '' (closedBall (x : ℂ) (r (x : ℂ)))) :=
            measure_biUnion_le _ ht_count _
    -- Per-ball Morrey/volume bound.
    have hper : ∀ x : t,
        volume (f '' (closedBall (x : ℂ) (r (x : ℂ))))
          ≤ K * (a x) ^ (1 - 2 / p) * (e x) ^ (2 / p) := by
      intro x
      have hrx : 0 < r (x : ℂ) := hr_pos x x.2
      -- `g` is integrable on the doubled ball (inside `closedBall 0 (R+1)`).
      have hgInt : IntegrableOn g (ball (x : ℂ) (2 * r (x : ℂ))) volume := by
        apply hgInt_cb.mono_set
        exact (hball_in_U x x.2).trans (hUcb.trans hball_cb)
      -- The verified per-ball bound.
      have hbound :
          volume (f '' (closedBall (x : ℂ) (r (x : ℂ))))
            ≤ ENNReal.ofReal (C ^ 2 * Real.pi) * (ENNReal.ofReal (r (x : ℂ))) ^ (2 - 4 / p)
              * (∫⁻ z in ball (x : ℂ) (2 * r (x : ℂ)), G z) ^ (2 / p) := by
        set xr : ℝ := r (x : ℂ) with hxr
        set xc : ℂ := (x : ℂ) with hxc
        set I : ℝ := ∫ z in ball xc (2 * xr), g z with hI
        have hI0 : 0 ≤ I := integral_nonneg hg_nonneg
        set ρ : ℝ := C * xr ^ (1 - 2 / p) * I ^ (1 / p) with hρ
        have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
        have hsub : f '' (closedBall xc xr) ⊆ closedBall (f xc) ρ := by
          rintro w ⟨y, hy, rfl⟩
          rw [mem_closedBall, dist_comm, Complex.dist_eq, ← norm_sub_rev]
          have := hMor xc xr hrx y hy
          rw [show (∫ z in ball xc (2 * xr), ‖gx z‖ ^ p + ‖gy z‖ ^ p) = I from rfl,
            ← hρ] at this
          exact this
        have hvol : volume (f '' (closedBall xc xr))
            ≤ ENNReal.ofReal ρ ^ 2 * (NNReal.pi : ℝ≥0∞) :=
          (measure_mono hsub).trans (le_of_eq (volume_closedBall _ _))
        refine le_trans hvol ?_
        have harith : (ENNReal.ofReal ρ) ^ 2 * (NNReal.pi : ℝ≥0∞)
            = ENNReal.ofReal (C ^ 2 * Real.pi) * (ENNReal.ofReal xr) ^ (2 - 4 / p)
              * (ENNReal.ofReal I) ^ (2 / p) := by
          rw [hρ, ← ENNReal.ofReal_pow (by positivity)]
          have hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
            rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
          rw [hpi, ← ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_rpow_of_pos hrx, ENNReal.ofReal_rpow_of_nonneg hI0 (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [mul_pow, mul_pow, ← Real.rpow_natCast (xr ^ (1 - 2 / p)) 2,
            ← Real.rpow_natCast (I ^ (1 / p)) 2, ← Real.rpow_mul hrx.le, ← Real.rpow_mul hI0]
          push_cast; ring_nf
        rw [harith]
        have hconv : ENNReal.ofReal I = ∫⁻ z in ball xc (2 * xr), G z := by
          rw [hI, hGdef]
          exact ofReal_integral_eq_lintegral_ofReal hgInt (ae_of_all _ hg_nonneg)
        rw [hconv]
      -- Convert `(ofReal r)^(2-4/p)` into `a x ^ (1-2/p)`.
      have hax : a x = (ENNReal.ofReal (r (x : ℂ))) ^ 2 := rfl
      have hconv_a : (ENNReal.ofReal (r (x : ℂ))) ^ (2 - 4 / p) = (a x) ^ (1 - 2 / p) := by
        rw [hax, ← ENNReal.rpow_natCast (ENNReal.ofReal (r (x : ℂ))) 2, ← ENNReal.rpow_mul]
        congr 1
        push_cast; ring
      rw [hconv_a] at hbound
      exact hbound
    -- Sum the per-ball bounds.
    have hsum_per : ∑' x : t, volume (f '' (closedBall (x : ℂ) (r (x : ℂ))))
        ≤ ∑' x : t, K * (a x) ^ (1 - 2 / p) * (e x) ^ (2 / p) :=
      ENNReal.tsum_le_tsum hper
    -- Pull out `K` and apply discrete Hölder.
    have hfactor : ∑' x : t, K * (a x) ^ (1 - 2 / p) * (e x) ^ (2 / p)
        = K * ∑' x : t, (a x) ^ (1 - 2 / p) * (e x) ^ (2 / p) := by
      rw [← ENNReal.tsum_mul_left]; congr 1; ext x; ring
    -- Discrete Hölder over the countable index `t`.
    have hHolder : ∑' x : t, (a x) ^ (1 / P) * (e x) ^ (1 / Q)
        ≤ (∑' x : t, a x) ^ (1 / P) * (∑' x : t, e x) ^ (1 / Q) := by
      let this : MeasurableSpace t := ⊤
      have : MeasurableSingletonClass t := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
      have hmeas : ∀ (φ : t → ℝ≥0∞), AEMeasurable φ (Measure.count) :=
        fun φ => measurable_from_top.aemeasurable
      have key := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure t) hPQ
        (f := fun x => (a x) ^ (1 / P)) (g := fun x => (e x) ^ (1 / Q)) (hmeas _) (hmeas _)
      simp only [lintegral_count] at key
      have hrwP : ∀ x, ((a x) ^ (1 / P)) ^ P = a x := fun x => by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hPpos.ne', ENNReal.rpow_one]
      have hrwQ : ∀ x, ((e x) ^ (1 / Q)) ^ Q = e x := fun x => by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hQpos.ne', ENNReal.rpow_one]
      simp only [Pi.mul_apply, hrwP, hrwQ] at key
      exact key
    -- Rewrite the Hölder exponents `1/P = 1-2/p`, `1/Q = 2/p`.
    rw [hPinv, hQinv] at hHolder
    -- The energy multiplicity bound (from the bounded-overlap cover).
    have hEnergy' : ∑' x : t, e x ≤ (M : ℝ≥0∞) * (∫⁻ z in U, G z) := by
      have : ((M : ℕ) : ℝ≥0∞) = (58 : ℝ≥0∞) := by rw [hMdef]; norm_num
      rw [this]; exact hEnergy
    -- The total ball measure bound: `∑' a x ≤ ε / π`.
    have ha_sum : ∑' x : t, a x ≤ ε * (ENNReal.ofReal Real.pi)⁻¹ := by
      have hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
        rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
      have hπpos : (0 : ℝ≥0∞) < ENNReal.ofReal Real.pi := by
        rw [ENNReal.ofReal_pos]; exact Real.pi_pos
      -- `vol (closedBall x (r x)) = a x * π`.
      have hvol_eq : ∀ x : t,
          volume (closedBall (x : ℂ) (r (x : ℂ))) = a x * ENNReal.ofReal Real.pi := by
        intro x
        have hax : a x = (ENNReal.ofReal (r (x : ℂ))) ^ 2 := rfl
        rw [volume_closedBall, hax, hpi]
      have : (∑' x : t, a x) * ENNReal.ofReal Real.pi ≤ ε := by
        rw [← ENNReal.tsum_mul_right]
        calc ∑' x : t, a x * ENNReal.ofReal Real.pi
            = ∑' x : t, volume (closedBall (x : ℂ) (r (x : ℂ))) := by
              congr 1; ext x; rw [hvol_eq]
          _ ≤ volume S + ε := htsum
          _ = ε := by rw [hSnull, zero_add]
      -- divide by π.
      rw [← ENNReal.le_div_iff_mul_le (Or.inl hπpos.ne') (Or.inl ENNReal.ofReal_ne_top)] at this
      rw [ENNReal.div_eq_inv_mul] at this
      rwa [mul_comm] at this
    -- Assemble.
    calc volume (f '' S)
        ≤ ∑' x : t, volume (f '' (closedBall (x : ℂ) (r (x : ℂ)))) := himg_cov
      _ ≤ K * ∑' x : t, (a x) ^ (1 - 2 / p) * (e x) ^ (2 / p) := by
            rw [← hfactor]; exact hsum_per
      _ ≤ K * ((∑' x : t, a x) ^ (1 - 2 / p) * (∑' x : t, e x) ^ (2 / p)) :=
            mul_le_mul' le_rfl hHolder
      _ ≤ K * ((ε * (ENNReal.ofReal Real.pi)⁻¹) ^ (1 - 2 / p)
              * ((M : ℝ≥0∞) * (∫⁻ z in U, G z)) ^ (2 / p)) := by
            refine mul_le_mul' le_rfl (mul_le_mul' ?_ ?_)
            · exact ENNReal.rpow_le_rpow ha_sum hθpos.le
            · exact ENNReal.rpow_le_rpow hEnergy' hp_2p.le
      _ = Kη * (ε * (ENNReal.ofReal Real.pi)⁻¹) ^ (1 - 2 / p) := by
            rw [hKηdef]; ring
  -- Let `ε → 0`.
  have hzero : volume (f '' S) = 0 := by
    set K' : ℝ≥0∞ := Kη * (ENNReal.ofReal Real.pi)⁻¹ ^ (1 - 2 / p) with hK'def
    have hKη' : K' ≠ ⊤ := by
      rw [hK'def]
      refine ENNReal.mul_ne_top hKη_ne_top (ENNReal.rpow_ne_top_of_nonneg hθpos.le ?_)
      rw [Ne, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero]
      linarith [Real.pi_pos]
    have hbnd : ∀ ε : ℝ≥0∞, 0 < ε → volume (f '' S) ≤ K' * ε ^ (1 - 2 / p) := by
      intro ε hε
      have h := hMainBound ε hε
      rw [ENNReal.mul_rpow_of_nonneg _ _ hθpos.le] at h
      calc volume (f '' S)
          ≤ Kη * (ε ^ (1 - 2 / p) * (ENNReal.ofReal Real.pi)⁻¹ ^ (1 - 2 / p)) := h
        _ = K' * ε ^ (1 - 2 / p) := by rw [hK'def]; ring
    -- the ε→0 argument
    have hlim : Filter.Tendsto (fun ε : ℝ≥0∞ => K' * ε ^ (1 - 2 / p))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h1 : Filter.Tendsto (fun ε : ℝ≥0∞ => ε ^ (1 - 2 / p)) (nhds 0) (nhds 0) := by
        have hc := ENNReal.continuous_rpow_const (y := 1 - 2 / p)
        have := hc.tendsto 0
        rwa [ENNReal.zero_rpow_of_pos hθpos] at this
      have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr hKη')
      rw [mul_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    have hle0 : volume (f '' S) ≤ 0 := by
      apply ge_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hbnd ε hε
    simpa using hle0
  exact hzero

end NoWanderingDomains
