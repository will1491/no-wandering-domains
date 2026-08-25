/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Abstract Cotlar-Stein almost-orthogonality lemma

Finite Cotlar-Stein lemma for a finite family of bounded operators on a Hilbert
space: if `T : Fin N -> (H ->L[C] H)` satisfies the two Schur bounds
`forall i, sum j sqrt ‖(T i)* (T j)‖ <= A` and
`forall i, sum j sqrt ‖(T i) (T j)*‖ <= A`, then `‖sum i, T i‖ <= A`.

## Proof outline

With `S = sum i, T i` and `R = star S * S` (self-adjoint), for every `n` the
C*-identity gives `‖S‖ ^ (2 * 2^n) = ‖R ^ (2^n)‖`. Expanding `R ^ (2^n)` over
alternating chains of operators, each chain is bounded two ways (by grouping
adjacent factors as `(T i)* (T j)` or as `(T j) (T i')*`); the geometric mean of
the two bounds and a transfer-matrix telescoping over the Schur estimates give
`‖S‖ ^ (2 * 2^n) <= (Mb * N) * A ^ (2 * 2^n - 1)`, where `Mb` is any uniform
bound on the `‖T i‖`. Letting `n -> infinity` forces `‖S‖ <= A`.
-/

namespace NoWanderingDomains.SingularIntegral

/-- Non-commutative expansion of a power of a finite sum as a sum of ordered
products indexed by functions `Fin m -> ι`. -/
theorem noncomm_sum_pow {M : Type*} [Ring M] {ι : Type*} [Fintype ι]
    (g : ι → M) (m : ℕ) :
    (∑ x, g x) ^ m = ∑ p : Fin m → ι, (List.ofFn (fun k => g (p k))).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, Finset.sum_mul]
      rw [← (Fin.snocEquiv (fun _ : Fin (m+1) => ι)).sum_comp]
      simp only [Fin.snocEquiv_apply]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [List.ofFn_succ', List.prod_concat]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- Reassociation of an ordered product of pairs:
`prod (a k * b k) = a 0 * (prod (b k.castSucc * a k.succ)) * b last`. -/
theorem chain_regroup {M : Type*} [Monoid M] (m : ℕ) (a b : Fin (m + 1) → M) :
    (List.ofFn (fun k => a k * b k)).prod
      = a 0 * (List.ofFn (fun k : Fin m => b k.castSucc * a k.succ)).prod * b (Fin.last m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ' (fun k => a k * b k), List.prod_concat]
      rw [ih (fun k => a k.castSucc) (fun k => b k.castSucc)]
      rw [List.ofFn_succ' (fun k : Fin (m+1) => b k.castSucc * a k.succ), List.prod_concat]
      simp only [Fin.castSucc_zero, Fin.succ_castSucc, Fin.succ_last, mul_assoc]

/-- `sqrt` of an ordered product of nonnegative reals is the ordered product of
the `sqrt`s. -/
theorem sqrt_prod_ofFn {n : ℕ} (f : Fin n → ℝ) (hf : ∀ k, 0 ≤ f k) :
    Real.sqrt (List.ofFn (fun k => f k)).prod = (List.ofFn (fun k => Real.sqrt (f k))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ', List.prod_concat, Real.sqrt_mul,
        ih (fun k => f k.castSucc) (fun k => hf _)]
      · rw [List.ofFn_succ' (fun k => Real.sqrt (f k)), List.prod_concat]
      · exact List.prod_nonneg
          (by simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
              exact fun k => hf _)

/-- Geometric-mean estimate: `x ≤ a`, `x ≤ b`, `0 ≤ x` imply `x ≤ √a * √b`. -/
theorem geom_mean_le (x a b : ℝ) (hx : 0 ≤ x) (ha : x ≤ a) (hb : x ≤ b) :
    x ≤ Real.sqrt a * Real.sqrt b := by
  have h0a : 0 ≤ a := le_trans hx ha
  rw [← Real.sqrt_mul h0a, show x = Real.sqrt (x*x) from (Real.sqrt_mul_self hx).symm]
  exact Real.sqrt_le_sqrt (mul_le_mul ha hb hx h0a)

/-- Reindex a sum over `Fin (m+2) -> Fin N` by splitting off the last coordinate. -/
theorem reindex_snoc {N m : ℕ} (f : (Fin (m + 2) → Fin N) → ℝ) :
    (∑ i : Fin (m+2) → Fin N, f i)
      = ∑ i' : Fin (m+1) → Fin N, ∑ iL : Fin N, f (Fin.snoc i' iL) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (m+2) => Fin N)).sum_comp (g := f),
    Fintype.sum_prod_type_right]
  rfl

/-- Reindex a double sum over chains by splitting off the last coordinate of each. -/
theorem reindex_double {N m : ℕ} (S : (Fin (m + 2) → Fin N) → (Fin (m + 2) → Fin N) → ℝ) :
    (∑ i : Fin (m+2) → Fin N, ∑ j : Fin (m+2) → Fin N, S i j)
      = ∑ i' : Fin (m+1) → Fin N, ∑ j' : Fin (m+1) → Fin N,
          ∑ iL : Fin N, ∑ jL : Fin N,
            S (Fin.snoc i' iL) (Fin.snoc j' jL) := by
  rw [reindex_snoc (fun i => ∑ j, S i j)]
  apply Finset.sum_congr rfl; intro i' _
  rw [show (∑ iL : Fin N, ∑ j : Fin (m+2) → Fin N, S (Fin.snoc i' iL) j)
      = ∑ iL : Fin N, ∑ j' : Fin (m+1) → Fin N, ∑ jL : Fin N,
          S (Fin.snoc i' iL) (Fin.snoc j' jL) from ?_]
  · rw [Finset.sum_comm]
  · apply Finset.sum_congr rfl; intro iL _
    rw [reindex_snoc (fun j => S (Fin.snoc i' iL) j)]

/-- Inner per-`(i',j')` estimate used in the telescoping induction step. -/
theorem chain_inner_step {N : ℕ} (A : ℝ) (hA0 : 0 ≤ A) (β γ : Fin N → Fin N → ℝ)
    (hβ0 : ∀ i j, 0 ≤ β i j) (hγ0 : ∀ i j, 0 ≤ γ i j)
    (hβ : ∀ i, ∑ j, β i j ≤ A) (hγ : ∀ i, ∑ j, γ i j ≤ A) (m : ℕ)
    (i' j' : Fin (m + 1) → Fin N) :
    (∑ iL : Fin N, ∑ jL : Fin N,
        (List.ofFn (fun k : Fin (m+2) =>
            β ((Fin.snoc i' iL : Fin (m+2) → Fin N) k)
              ((Fin.snoc j' jL : Fin (m+2) → Fin N) k))).prod
          * (List.ofFn (fun k : Fin (m+1) =>
              γ ((Fin.snoc j' jL : Fin (m+2) → Fin N) k.castSucc)
                ((Fin.snoc i' iL : Fin (m+2) → Fin N) k.succ))).prod)
      ≤ A^2 * ((List.ofFn (fun k => β (i' k) (j' k))).prod
          * (List.ofFn (fun k : Fin m => γ (j' k.castSucc) (i' k.succ))).prod) := by
  set Bsmall := (List.ofFn (fun k => β (i' k) (j' k))).prod with hBsmall
  set Gsmall := (List.ofFn (fun k : Fin m => γ (j' k.castSucc) (i' k.succ))).prod with hGsmall
  have hBs0 : 0 ≤ Bsmall := List.prod_nonneg (by
    intro x hx; simp only [List.mem_ofFn] at hx; obtain ⟨k, rfl⟩ := hx; exact hβ0 _ _)
  have hGs0 : 0 ≤ Gsmall := List.prod_nonneg (by
    intro x hx; simp only [List.mem_ofFn] at hx; obtain ⟨k, rfl⟩ := hx; exact hγ0 _ _)
  have htransB : ∀ iL jL : Fin N,
      (List.ofFn (fun k : Fin (m+2) =>
          β ((Fin.snoc i' iL : Fin (m+2) → Fin N) k) ((Fin.snoc j' jL : Fin (m+2) → Fin N) k))).prod
        = Bsmall * β iL jL := by
    intro iL jL
    rw [hBsmall, List.ofFn_succ' (fun k : Fin (m+2) =>
        β ((Fin.snoc i' iL : Fin (m+2) → Fin N) k) ((Fin.snoc j' jL : Fin (m+2) → Fin N) k)),
      List.prod_concat]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have htransG : ∀ iL jL : Fin N,
      (List.ofFn (fun k : Fin (m+1) =>
          γ ((Fin.snoc j' jL : Fin (m+2) → Fin N) k.castSucc)
            ((Fin.snoc i' iL : Fin (m+2) → Fin N) k.succ))).prod
        = Gsmall * γ (j' (Fin.last m)) iL := by
    intro iL jL
    rw [hGsmall, List.ofFn_succ' (fun k : Fin (m+1) =>
        γ ((Fin.snoc j' jL : Fin (m+2) → Fin N) k.castSucc)
          ((Fin.snoc i' iL : Fin (m+2) → Fin N) k.succ)), List.prod_concat]
    have hbody : (fun k : Fin m =>
        γ ((Fin.snoc j' jL : Fin (m+2) → Fin N) (k.castSucc : Fin (m+1)).castSucc)
          ((Fin.snoc i' iL : Fin (m+2) → Fin N) (k.castSucc : Fin (m+1)).succ))
        = (fun k : Fin m => γ (j' k.castSucc) (i' k.succ)) := by
      funext k
      rw [show ((k.castSucc : Fin (m+1)).castSucc : Fin (m+2)) = (k.castSucc).castSucc from rfl,
        Fin.snoc_castSucc]
      rw [show ((k : Fin m).castSucc).succ = (k.succ).castSucc from (Fin.succ_castSucc k).symm,
        Fin.snoc_castSucc]
    rw [hbody]
    congr 1
    rw [Fin.snoc_castSucc, show ((Fin.last m).succ) = Fin.last (m+1) from Fin.succ_last m,
      Fin.snoc_last]
  simp_rw [htransB, htransG]
  have hrw : ∀ iL jL : Fin N,
      (Bsmall * β iL jL) * (Gsmall * γ (j' (Fin.last m)) iL)
        = (Bsmall * Gsmall) * (γ (j' (Fin.last m)) iL * β iL jL) := by
    intro iL jL; ring
  simp_rw [hrw]
  have hfactor : (∑ iL : Fin N, ∑ jL : Fin N,
        (Bsmall * Gsmall) * (γ (j' (Fin.last m)) iL * β iL jL))
      = (Bsmall * Gsmall) * (∑ iL : Fin N, ∑ jL : Fin N, γ (j' (Fin.last m)) iL * β iL jL) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro iL _
    rw [Finset.mul_sum]
  rw [hfactor, mul_comm (A^2) (Bsmall * Gsmall)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hinner : (∑ iL : Fin N, ∑ jL : Fin N, γ (j' (Fin.last m)) iL * β iL jL)
      = ∑ iL : Fin N, γ (j' (Fin.last m)) iL * (∑ jL : Fin N, β iL jL) := by
    apply Finset.sum_congr rfl
    intro iL _
    rw [Finset.mul_sum]
  rw [hinner]
  calc (∑ iL : Fin N, γ (j' (Fin.last m)) iL * (∑ jL : Fin N, β iL jL))
      ≤ ∑ iL : Fin N, γ (j' (Fin.last m)) iL * A := by
        apply Finset.sum_le_sum
        intro iL _
        exact mul_le_mul_of_nonneg_left (hβ iL) (hγ0 _ _)
    _ = (∑ iL : Fin N, γ (j' (Fin.last m)) iL) * A := by rw [Finset.sum_mul]
    _ ≤ A * A := mul_le_mul_of_nonneg_right (hγ (j' (Fin.last m))) hA0
    _ = A^2 := by ring

/-- Schur / transfer-matrix telescoping estimate. If two nonnegative kernels
`β γ : Fin N -> Fin N -> ℝ` have all row-sums bounded by `A`, then the
interleaved chain sum is bounded by `N * A ^ (2 m + 1)`. The chain has `m + 1`
`β`-factors and `m` `γ`-factors interleaved. -/
theorem chain_telescope {N : ℕ} (A : ℝ) (hA0 : 0 ≤ A) (β γ : Fin N → Fin N → ℝ)
    (hβ0 : ∀ i j, 0 ≤ β i j) (hγ0 : ∀ i j, 0 ≤ γ i j)
    (hβ : ∀ i, ∑ j, β i j ≤ A) (hγ : ∀ i, ∑ j, γ i j ≤ A) (m : ℕ) :
    ∑ i : Fin (m+1) → Fin N, ∑ j : Fin (m+1) → Fin N,
        (List.ofFn (fun k => β (i k) (j k))).prod
          * (List.ofFn (fun k : Fin m => γ (j k.castSucc) (i k.succ))).prod
      ≤ (N : ℝ) * A ^ (2 * m + 1) := by
  induction m with
  | zero =>
      simp only [List.ofFn_zero, List.prod_nil, mul_one, Nat.mul_zero, Nat.zero_add, pow_one]
      have hstep : ∀ (i j : Fin 1 → Fin N),
          (List.ofFn (fun k : Fin 1 => β (i k) (j k))).prod = β (i 0) (j 0) := by
        intro i j; simp [List.ofFn_succ]
      simp_rw [hstep]
      rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin N)).symm]
      simp only [Equiv.funUnique_symm_apply]
      have hj : ∀ a : Fin N, (∑ j : Fin 1 → Fin N, β a (j 0)) = ∑ b : Fin N, β a b := by
        intro a
        rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin N)).symm]
        simp only [Equiv.funUnique_symm_apply]
        rfl
      calc (∑ a : Fin N, ∑ j : Fin 1 → Fin N, β a (j 0))
          = ∑ a : Fin N, ∑ b : Fin N, β a b := by
            apply Finset.sum_congr rfl; intro a _; exact hj a
        _ ≤ ∑ a : Fin N, A := Finset.sum_le_sum (fun a _ => hβ a)
        _ = (N:ℝ) * A := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  | succ m ih =>
      rw [reindex_double (fun i j =>
        (List.ofFn (fun k => β (i k) (j k))).prod
          * (List.ofFn (fun k : Fin (m+1) => γ (j k.castSucc) (i k.succ))).prod)]
      calc (∑ i' : Fin (m+1) → Fin N, ∑ j' : Fin (m+1) → Fin N,
              ∑ iL : Fin N, ∑ jL : Fin N,
                (List.ofFn (fun k => β ((Fin.snoc i' iL : Fin (m+2) → Fin N) k)
                    ((Fin.snoc j' jL : Fin (m+2) → Fin N) k))).prod
                  * (List.ofFn (fun k : Fin (m+1) =>
                      γ ((Fin.snoc j' jL : Fin (m+2) → Fin N) k.castSucc)
                        ((Fin.snoc i' iL : Fin (m+2) → Fin N) k.succ))).prod)
          ≤ ∑ i' : Fin (m+1) → Fin N, ∑ j' : Fin (m+1) → Fin N,
              A^2 * ((List.ofFn (fun k => β (i' k) (j' k))).prod
                  * (List.ofFn (fun k : Fin m => γ (j' k.castSucc) (i' k.succ))).prod) := by
            apply Finset.sum_le_sum; intro i' _
            apply Finset.sum_le_sum; intro j' _
            exact chain_inner_step A hA0 β γ hβ0 hγ0 hβ hγ m i' j'
        _ = A^2 * (∑ i' : Fin (m+1) → Fin N, ∑ j' : Fin (m+1) → Fin N,
              (List.ofFn (fun k => β (i' k) (j' k))).prod
                  * (List.ofFn (fun k : Fin m => γ (j' k.castSucc) (i' k.succ))).prod) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i' _; rw [Finset.mul_sum]
        _ ≤ A^2 * ((N : ℝ) * A ^ (2 * m + 1)) := by
            apply mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (N : ℝ) * A ^ (2 * (m+1) + 1) := by
            rw [show 2 * (m+1) + 1 = (2 * m + 1) + 2 from by ring, pow_add]; ring

open ContinuousLinearMap

/-- Single-chain norm bound: an alternating product `∏ₖ (T iₖ)* (T jₖ)` is
controlled by `Mb` times the product of `√‖(T iₖ)* (T jₖ)‖` and the product of
`√‖(T jₖ) (T iₖ₊₁)*‖`, obtained from the two regroupings and the geometric mean. -/
theorem cotlarStein_perChain {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {N : ℕ} (T : Fin N → (H →L[ℂ] H)) (Mb : ℝ)
    (hMb : ∀ i, ‖T i‖ ≤ Mb) (hMb0 : 0 ≤ Mb) (m' : ℕ) (i j : Fin (m' + 1) → Fin N) :
    ‖(List.ofFn (fun k => (adjoint (T (i k))) ∘L (T (j k)))).prod‖
      ≤ Mb * ((List.ofFn (fun k => Real.sqrt ‖(adjoint (T (i k))) ∘L (T (j k))‖)).prod
            * (List.ofFn (fun k : Fin m' =>
                Real.sqrt ‖(T (j k.castSucc)) ∘L (adjoint (T (i k.succ)))‖)).prod) := by
  set chainN := ‖(List.ofFn (fun k => (adjoint (T (i k))) ∘L (T (j k)))).prod‖ with hchainN_def
  set prodBnorm := (List.ofFn (fun k => ‖(adjoint (T (i k))) ∘L (T (j k))‖)).prod with hprodB
  set prodCnorm :=
    (List.ofFn (fun k : Fin m' => ‖(T (j k.castSucc)) ∘L (adjoint (T (i k.succ)))‖)).prod
      with hprodC
  have hchainN0 : 0 ≤ chainN := norm_nonneg _
  have hprodC0 : 0 ≤ prodCnorm := List.prod_nonneg (by simp)
  -- bound (a): group adjacent factors as (T i)* (T j)
  have ha : chainN ≤ prodBnorm := by
    rw [hchainN_def, hprodB]
    have hne : (List.ofFn (fun k => (adjoint (T (i k))) ∘L (T (j k)))) ≠ [] := by simp
    calc ‖(List.ofFn (fun k => (adjoint (T (i k))) ∘L (T (j k)))).prod‖
        ≤ ((List.ofFn (fun k => (adjoint (T (i k))) ∘L (T (j k)))).map norm).prod :=
          List.norm_prod_le' hne
      _ = _ := by rw [List.map_ofFn]; rfl
  -- bound (b): group as (T i₀)*, then (T jₖ)(T iₖ₊₁)*, then (T jₗₐₛₜ)
  have hb : chainN ≤ ‖T (i 0)‖ * prodCnorm * ‖T (j (Fin.last m'))‖ := by
    rw [hchainN_def, hprodC]
    have hcomp : ∀ k, (adjoint (T (i k))) ∘L (T (j k)) = (adjoint (T (i k))) * (T (j k)) :=
      fun k => rfl
    simp only [hcomp]
    rw [chain_regroup m' (fun k => adjoint (T (i k))) (fun k => T (j k))]
    set A0 := adjoint (T (i 0))
    set Blast := T (j (Fin.last m'))
    set P := (List.ofFn (fun k : Fin m' => (T (j k.castSucc)) * (adjoint (T (i k.succ))))).prod
      with hP
    have hPbound : ‖P‖
        ≤ (List.ofFn (fun k : Fin m' => ‖(T (j k.castSucc)) ∘L (adjoint (T (i k.succ)))‖)).prod :=
          by
      rw [hP]
      rcases Nat.eq_zero_or_pos m' with hm0 | hmpos
      · subst hm0
        simp only [List.ofFn_zero, List.prod_nil]
        exact ContinuousLinearMap.norm_id_le
      · have hne :
            (List.ofFn (fun k : Fin m' => (T (j k.castSucc)) * (adjoint (T (i k.succ))))) ≠ [] := by
          simp [List.ofFn_eq_nil_iff]; omega
        calc ‖(List.ofFn (fun k : Fin m' => (T (j k.castSucc)) * (adjoint (T (i k.succ))))).prod‖
            ≤ ((List.ofFn (fun k : Fin m' =>
                (T (j k.castSucc)) * (adjoint (T (i k.succ))))).map norm).prod :=
              List.norm_prod_le' hne
          _ = _ := by rw [List.map_ofFn]; rfl
    calc ‖A0 * P * Blast‖
        ≤ ‖A0 * P‖ * ‖Blast‖ := norm_mul_le _ _
      _ ≤ (‖A0‖ * ‖P‖) * ‖Blast‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (‖A0‖ * (List.ofFn (fun k : Fin m' =>
            ‖(T (j k.castSucc)) ∘L (adjoint (T (i k.succ)))‖)).prod) * ‖Blast‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hPbound (norm_nonneg _)) (norm_nonneg _)
      _ = ‖T (i 0)‖ * (List.ofFn (fun k : Fin m' =>
            ‖(T (j k.castSucc)) ∘L (adjoint (T (i k.succ)))‖)).prod * ‖T (j (Fin.last m'))‖ := by
          rw [show ‖A0‖ = ‖T (i 0)‖ from
            LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint (T (i 0))]
  -- combine the two bounds via the geometric mean
  have htiz0 : 0 ≤ ‖T (i 0)‖ := norm_nonneg _
  have hsB : Real.sqrt prodBnorm
      = (List.ofFn (fun k => Real.sqrt ‖(adjoint (T (i k))) ∘L (T (j k))‖)).prod := by
    rw [hprodB]; exact sqrt_prod_ofFn _ (by simp)
  have hsC : Real.sqrt prodCnorm
      = (List.ofFn (fun k : Fin m' =>
          Real.sqrt ‖(T (j k.castSucc)) ∘L (adjoint (T (i k.succ)))‖)).prod := by
    rw [hprodC]; exact sqrt_prod_ofFn _ (by simp)
  have hgm := geom_mean_le chainN prodBnorm
    (‖T (i 0)‖ * prodCnorm * ‖T (j (Fin.last m'))‖) hchainN0 ha hb
  have hsqrtb : Real.sqrt (‖T (i 0)‖ * prodCnorm * ‖T (j (Fin.last m'))‖)
      = Real.sqrt ‖T (i 0)‖ * Real.sqrt prodCnorm * Real.sqrt ‖T (j (Fin.last m'))‖ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul htiz0]
  rw [hsqrtb] at hgm
  have hst : Real.sqrt ‖T (i 0)‖ ≤ Real.sqrt Mb := Real.sqrt_le_sqrt (hMb (i 0))
  have hsl : Real.sqrt ‖T (j (Fin.last m'))‖ ≤ Real.sqrt Mb := Real.sqrt_le_sqrt (hMb _)
  have key : Real.sqrt prodBnorm
        * (Real.sqrt ‖T (i 0)‖ * Real.sqrt prodCnorm * Real.sqrt ‖T (j (Fin.last m'))‖)
      ≤ Mb * ((List.ofFn (fun k => Real.sqrt ‖(adjoint (T (i k))) ∘L (T (j k))‖)).prod
            * (List.ofFn (fun k : Fin m' =>
                Real.sqrt ‖(T (j k.castSucc)) ∘L (adjoint (T (i k.succ)))‖)).prod) := by
    rw [← hsB, ← hsC]
    have hsmm : Real.sqrt Mb * Real.sqrt Mb = Mb := Real.mul_self_sqrt hMb0
    calc Real.sqrt prodBnorm
          * (Real.sqrt ‖T (i 0)‖ * Real.sqrt prodCnorm * Real.sqrt ‖T (j (Fin.last m'))‖)
        ≤ Real.sqrt prodBnorm * (Real.sqrt Mb * Real.sqrt prodCnorm * Real.sqrt Mb) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          apply mul_le_mul _ hsl (Real.sqrt_nonneg _) (by positivity)
          exact mul_le_mul hst (le_refl _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Mb * (Real.sqrt prodBnorm * Real.sqrt prodCnorm) := by
          have e : Real.sqrt prodBnorm * (Real.sqrt Mb * Real.sqrt prodCnorm * Real.sqrt Mb)
              = (Real.sqrt Mb * Real.sqrt Mb) * (Real.sqrt prodBnorm * Real.sqrt prodCnorm) := by
            ring
          rw [e, hsmm]
  exact le_trans hgm key

/-- **Finite Cotlar-Stein almost-orthogonality lemma.** -/
theorem cotlarStein {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {N : ℕ} (T : Fin N → (H →L[ℂ] H)) (A : ℝ) (hA : 0 ≤ A)
    (hAdjMul : ∀ i, ∑ j, Real.sqrt ‖(ContinuousLinearMap.adjoint (T i)) ∘L (T j)‖ ≤ A)
    (hMulAdj : ∀ i, ∑ j, Real.sqrt ‖(T i) ∘L (ContinuousLinearMap.adjoint (T j))‖ ≤ A) :
    ‖∑ i, T i‖ ≤ A := by
  classical
  set S : H →L[ℂ] H := ∑ i, T i with hS
  -- uniform bound on ‖T i‖
  obtain ⟨Mb, hMb0, hMb⟩ : ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ i, ‖T i‖ ≤ Mb :=
    ⟨∑ i, ‖T i‖, Finset.sum_nonneg (fun i _ => norm_nonneg _),
      fun i => Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ i)⟩
  -- expand R = star S * S as a double sum
  have hadjS : adjoint S = ∑ i, adjoint (T i) := map_sum (adjoint) T Finset.univ
  have hRexp : star S * S = ∑ p : Fin N × Fin N, (adjoint (T p.1)) ∘L (T p.2) := by
    rw [ContinuousLinearMap.star_eq_adjoint, hadjS]
    change (∑ i, adjoint (T i)) ∘L (∑ j, T j) = _
    rw [Fintype.sum_prod_type, ContinuousLinearMap.finsetSum_comp]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ContinuousLinearMap.comp_finsetSum]
  -- KEY BOUND: ‖(star S * S) ^ (m'+1)‖ ≤ Mb * (N * A ^ (2 m' + 1))
  have keyBound : ∀ m' : ℕ, ‖(star S * S) ^ (m'+1)‖ ≤ Mb * ((N : ℝ) * A ^ (2 * m' + 1)) := by
    intro m'
    set β : Fin N → Fin N → ℝ := fun a b => Real.sqrt ‖(adjoint (T a)) ∘L (T b)‖ with hβ_def
    set γ : Fin N → Fin N → ℝ := fun a b => Real.sqrt ‖(T a) ∘L (adjoint (T b))‖ with hγ_def
    have step1 : ‖(star S * S) ^ (m'+1)‖
        ≤ ∑ P : Fin (m'+1) → Fin N × Fin N,
            ‖(List.ofFn (fun k => (adjoint (T (P k).1)) ∘L (T (P k).2))).prod‖ := by
      rw [hRexp, noncomm_sum_pow]
      exact le_trans (norm_sum_le _ _) (le_of_eq rfl)
    have step2 :
        (∑ P : Fin (m'+1) → Fin N × Fin N,
            ‖(List.ofFn (fun k => (adjoint (T (P k).1)) ∘L (T (P k).2))).prod‖)
        ≤ Mb * (∑ i : Fin (m'+1) → Fin N, ∑ j : Fin (m'+1) → Fin N,
            (List.ofFn (fun k => β (i k) (j k))).prod
              * (List.ofFn (fun k : Fin m' => γ (j k.castSucc) (i k.succ))).prod) := by
      rw [Finset.mul_sum]
      rw [← Equiv.sum_comp
        (Equiv.arrowProdEquivProdArrow (Fin (m'+1)) (fun _ => Fin N) (fun _ => Fin N)).symm]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_le_sum
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      change ‖(List.ofFn (fun k => (adjoint (T (i k))) ∘L (T (j k)))).prod‖ ≤ _
      exact cotlarStein_perChain T Mb hMb hMb0 m' i j
    have step3 :
        (∑ i : Fin (m'+1) → Fin N, ∑ j : Fin (m'+1) → Fin N,
            (List.ofFn (fun k => β (i k) (j k))).prod
              * (List.ofFn (fun k : Fin m' => γ (j k.castSucc) (i k.succ))).prod)
        ≤ (N : ℝ) * A ^ (2 * m' + 1) := by
      apply chain_telescope A hA β γ
      · intro a b; exact Real.sqrt_nonneg _
      · intro a b; exact Real.sqrt_nonneg _
      · intro a; exact hAdjMul a
      · intro a; exact hMulAdj a
    calc ‖(star S * S) ^ (m'+1)‖ ≤ _ := step1
      _ ≤ Mb * _ := step2
      _ ≤ Mb * ((N : ℝ) * A ^ (2 * m' + 1)) := mul_le_mul_of_nonneg_left step3 hMb0
  -- recast keyBound as ‖S‖ ^ (2 * 2^n) ≤ (Mb * N) * A ^ (2 * 2^n - 1)
  have powBound : ∀ n : ℕ, ‖S‖ ^ (2 * 2^n) ≤ (Mb * (N : ℝ)) * A ^ (2 * 2^n - 1) := by
    intro n
    have h2n : 2^n = (2^n - 1) + 1 := by have : 1 ≤ 2^n := Nat.one_le_two_pow; omega
    have hnorm : ‖(star S * S) ^ 2^n‖ = ‖S‖ ^ (2 * 2^n) := by
      rw [(IsSelfAdjoint.star_mul_self S).norm_pow_two_pow n, CStarRing.norm_star_mul_self,
        ← sq, ← pow_mul, mul_comm]
    have hkey := keyBound (2^n - 1)
    rw [← h2n] at hkey
    rw [hnorm] at hkey
    have hexp : 2 * (2^n - 1) + 1 = 2 * 2^n - 1 := by
      have : 1 ≤ 2^n := Nat.one_le_two_pow; omega
    rw [hexp] at hkey
    calc ‖S‖ ^ (2 * 2^n) ≤ Mb * ((N : ℝ) * A ^ (2 * 2^n - 1)) := hkey
      _ = (Mb * (N : ℝ)) * A ^ (2 * 2^n - 1) := by ring
  -- limit/contradiction argument: ‖S‖ ≤ A
  set x := ‖S‖ with hx_def
  set C := Mb * (N : ℝ) with hC_def
  have hC0 : 0 ≤ C := by rw [hC_def]; positivity
  have hx0 : 0 ≤ x := norm_nonneg _
  by_contra hlt
  rw [not_le] at hlt
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hxpos : 0 < x := lt_of_le_of_lt hA hlt
    have h2 := powBound 0
    simp only [pow_zero, mul_one] at h2
    rw [← hA0] at h2
    norm_num at h2
    nlinarith [pow_pos hxpos 2]
  · have hr : 1 < x / A := (one_lt_div hApos).mpr hlt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C / A) hr
    have hexp : k ≤ 2 * 2^k :=
      le_trans (Nat.le_of_lt (Nat.lt_two_pow_self)) (by nlinarith [Nat.one_le_two_pow (n := k)])
    have hH := powBound k
    have hdiv : (x / A) ^ (2 * 2^k) ≤ C / A := by
      rw [div_pow, div_le_div_iff₀ (by positivity) hApos]
      calc x ^ (2 * 2^k) * A ≤ (C * A ^ (2 * 2^k - 1)) * A :=
            mul_le_mul_of_nonneg_right hH hA
        _ = C * (A ^ (2 * 2^k - 1) * A) := by ring
        _ = C * A ^ (2 * 2^k - 1 + 1) := by rw [pow_succ]
        _ = C * A ^ (2 * 2^k) := by
            congr 2
            have h1 : 1 ≤ 2^k := Nat.one_le_two_pow
            omega
    have hmono : (x / A) ^ k ≤ (x / A) ^ (2 * 2^k) :=
      pow_le_pow_right₀ (le_of_lt hr) hexp
    have : C / A < (x / A) ^ (2 * 2^k) := lt_of_lt_of_le hk hmono
    linarith

end NoWanderingDomains.SingularIntegral
