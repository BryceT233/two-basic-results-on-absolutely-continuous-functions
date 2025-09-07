/-
Copyright (c) 2025 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open MeasureTheory Filter

-- The Fundamental Theorem of Calculus for absolutely continuous functions
theorem absolutelyContinuous_FTC (g : ℝ → ℂ) (hg : ∀ a b, IntervalIntegrable g volume a b) (s : ℝ) :
    let F := fun t => ∫ (x : ℝ) in s..t, g x; ∀ᵐ x, HasDerivAt F (g x) x := by
-- Apply Lebesgue's Differentiation theorem `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub` to $g$
  intro F; have avg : LocallyIntegrable g volume := by
    intro x; use Set.Ioc (x - 1) (x + 1); constructor
    · rw [mem_nhds_iff_exists_Ioo_subset]
      use x - 1, x + 1; simp [Set.Ioo_subset_Ioc_self]
    specialize hg (x - 1) (x + 1); rw [IntervalIntegrable] at hg
    exact hg.left
  apply IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub at avg
  specialize avg 1; rw [ae_iff] at *
  rw [eq_iff_le_not_lt]; constructor
  -- Prove that the goal holds true for all Lebesgue points of $g$
  · rw [← avg]; apply measure_mono
    rw [Set.subset_def]; intro x
    simp only [Set.mem_setOf_eq, one_mul, Metric.mem_closedBall, not_forall, exists_prop]
    contrapose!; intro h; specialize h ℕ atTop
  -- Rewrite the derivative goal to a limit goal of a sequence $u$
    simp only [hasDerivAt_iff_tendsto, Real.norm_eq_abs, Complex.real_smul, Complex.ofReal_sub]
    apply tendsto_of_seq_tendsto
    intro u hu; simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, Function.comp_apply,
      dist_zero_right, norm_mul, norm_inv, Real.norm_eq_abs, abs_abs]
    simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, Real.dist_eq] at hu
    by_cases aux : (setOf fun n => u n ≠ x).Finite
    -- If $u_n ≠ x$ holds true for only finitely many $n$'s, the goal is trivial since $u$ is eventually a constant sequence
    · suffices : ∃ N, ∀ n ≥ N, u n = x
      · rcases this with ⟨N, hN⟩; intros
        use N; intro n nge
        simp only [← hN n nge, sub_self, abs_zero, inv_zero, zero_mul, norm_zero, mul_zero]
        assumption
      by_cases h : {n | u n ≠ x} = ∅
      · simp only [ne_eq, Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        Decidable.not_not] at h
        simp [h]
      rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at h
      replace h : aux.toFinset.Nonempty := by
        simp only [ne_eq, Set.Finite.toFinset_nonempty]; exact h
      let m := aux.toFinset.max' h
      use m + 1; intro n nge; suffices : n ∉ aux.toFinset
      · simp only [ne_eq, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Decidable.not_not] at this
        exact this
      revert nge; contrapose!; intro h
      have := Finset.le_max' aux.toFinset _ h; omega
  -- If there are infinitely many terms $u_n ≠ x$, denote this subsequence by $u'$
    rw [← Set.Infinite] at aux
    have u'_range := Nat.range_nth_of_infinite aux
    simp only [ne_eq, Set.ext_iff, Set.mem_range, Set.mem_setOf_eq] at u'_range
    let u' := u ∘ Nat.nth (fun n => u n ≠ x)
    have u'ne := Nat.nth_mem_of_infinite aux
  -- Define a center function $w$ and a radius function $δ$, prove two auxillary lemma that helps specializing the Lebesgue's Differentiation theorem `h`
    let w : ℕ → ℝ := fun n => (x + u' n) / 2
    let δ : ℕ → ℝ := fun n => |x - u' n| / 2
    have aux_δ : Tendsto δ atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [nhdsWithin, tendsto_inf]; constructor
      · rw [Metric.tendsto_atTop]; intro ε εpos
        norm_num [δ, u']; specialize hu (2 * ε) (by positivity)
        rcases hu with ⟨N, hN⟩
        use N; intro n nge; rw [abs_sub_comm, div_lt_iff₀']
        apply hN; apply le_trans nge
        apply Nat.le_nth
        · intro; contradiction
        norm_num
      simp [δ]; use 0; simp only [zero_le, ne_eq, Function.comp_apply, forall_const, u']
      intro n; rw [sub_eq_zero, ← ne_eq]; symm; apply u'ne
    have aux'_wδ : ∀ᶠ (j : ℕ) in atTop, dist x (w j) ≤ δ j := by
      norm_num [w, δ, Real.dist_eq]; use 0
      simp only [zero_le, forall_const]
      intro; ring_nf; field_simp
      norm_num [abs_div, ← sub_eq_add_neg]
  -- Specialize `h` to $w$ and $δ$, them simplify `h`
    specialize h w δ aux_δ aux'_wδ
    simp only [average, Metric.closedBall, Real.dist_eq, MeasurableSet.univ, Measure.restrict_apply,
      Set.univ_inter, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, Metric.tendsto_atTop,
      gt_iff_lt, ge_iff_le, dist_zero_right, norm_mul, norm_inv, Real.norm_eq_abs,
      ENNReal.abs_toReal, w, δ] at h
    simp only [abs_le, le_sub_iff_add_le, sub_le_iff_le_add, ← Set.mem_Icc] at h
    simp only [Set.setOf_mem_eq, Real.volume_Icc] at h
    ring_nf at h; field_simp at h
  -- Take any $ε > 0$, specialize `h` to $ε$ to get some number $N$
    intro ε εpos; specialize h ε εpos; rcases h with ⟨N, hN⟩
  -- Fulfill the goal with $Nat.nth (fun n => u n ≠ x) N$ and prove the inequality by computations
    use Nat.nth (fun n => u n ≠ x) N; intro n nge; dsimp [F]
    rw [intervalIntegral.integral_interval_sub_interval_comm, intervalIntegral.integral_same]
    rw [zero_sub, intervalIntegral, neg_sub, ← intervalIntegral]
    have : ∫ u in x..(u n), g x = (u n - x) * g x := by simp
    rw [← this, ← intervalIntegral.integral_sub, intervalIntegral]
    by_cases h : u n = x; simp [h]; exact εpos
    obtain ⟨m, hm⟩ := (u'_range n).mpr h
    rw [← hm, (Nat.nth_strictMono aux).le_iff_le] at nge
    rw [← ne_eq, ne_iff_lt_or_gt] at h; rw [inv_mul_eq_div]
    simp [u'] at hN; rcases h with h|h
    · rw [Set.Ioc_eq_empty]
      simp only [Measure.restrict_empty, integral_zero_measure, zero_sub, norm_neg, abs_norm, gt_iff_lt]
      rw [abs_sub_comm]; specialize hN m nge
      rw [hm, abs_eq_self.mpr, abs_eq_self.mpr] at hN
      ring_nf at hN; rw [mul_comm, inv_mul_eq_div] at hN
      apply lt_of_le_of_lt _ hN; gcongr
      any_goals linarith only [h]
      · rw [integral_Icc_eq_integral_Ioc]
        apply norm_integral_le_integral_norm
      · apply le_abs_self
      positivity
    nth_rw 2 [Set.Ioc_eq_empty]
    simp only [Measure.restrict_empty, integral_zero_measure, sub_zero, abs_norm, gt_iff_lt]
    specialize hN m nge; rw [hm, abs_eq_self.mpr, abs_eq_neg_self.mpr] at hN
    ring_nf at hN; rw [abs_eq_self.mpr]
    rw [← sub_eq_neg_add, mul_comm, inv_mul_eq_div] at hN
    apply lt_of_le_of_lt _ hN; gcongr
    any_goals linarith only [h]
    · rw [integral_Icc_eq_integral_Ioc]
      apply norm_integral_le_integral_norm
    positivity; any_goals apply hg
    simp
  push_neg; apply zero_le

-- Prove that we can flip the limit of a double integral
lemma integral_integral_flip (f g : ℝ → ℂ) (a b : ℝ) (hf : IntegrableOn f (Set.Icc a b))
    (hg : IntegrableOn g (Set.Icc a b)) : ∫ x in Set.Icc a b, ∫ y in Set.Icc x b, f x * g y =
    ∫ x in Set.Icc a b, ∫ y in Set.Icc a x, f y * g x := by
-- Prove two measurability facts for later use
  have aux_mea : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc p.1 b} := by
    have : {p | p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc p.1 b} = Set.Icc a b ×ˢ Set.Icc a b ∩
    (fun p => p.2 - p.1) ⁻¹' (Set.Ici 0) := by
      simp [Set.ext_iff]; intro x y; constructor
      · rintro ⟨⟨⟩,⟨⟩⟩; split_ands; any_goals assumption
        linarith
      rintro ⟨⟨⟨⟩,⟨⟩⟩⟩; split_ands; all_goals assumption
    rw [this]; measurability
  have aux_mea' : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a p.1} := by
    have : {p | p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a p.1} = Set.Icc a b ×ˢ Set.Icc a b ∩
    (fun p => p.2 - p.1) ⁻¹' (Set.Iic 0) := by
      simp [Set.ext_iff]; intro x y; constructor
      · rintro ⟨⟨⟩,⟨⟩⟩; split_ands; any_goals assumption
        linarith
      rintro ⟨⟨⟨⟩,⟨⟩⟩⟩; split_ands; all_goals assumption
    rw [this]; measurability
  calc
  _ = ∫ (p : ℝ × ℝ) in {p | p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc p.1 b}, f p.1 * g p.2 ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc a b)) := by
  -- Apply Fubini's Theorem to convert LHS to an integral on the product space
    nth_rw 2 [← integral_indicator]; rw [integral_prod]
    apply setIntegral_congr_fun; exact measurableSet_Icc
    · intro x hx; simp only
      rw [← integral_indicator, ← integral_indicator]
      apply integral_congr_ae
      · rw [EventuallyEq]; apply ae_of_all
        intro y; rw [Set.indicator_apply]; split_ifs with hy
        · rw [Set.indicator_of_mem, Set.indicator_of_mem]; simp only [Set.mem_setOf_eq]
          exact ⟨hx, hy⟩
          · rw [Set.mem_Icc] at *
            exact ⟨by linarith only [hx.left, hy.left], hy.right⟩
        rw [Set.indicator_apply]; split_ifs with hy'
        · rw [Set.indicator_of_notMem]; simp only [Set.mem_setOf_eq, not_and]
          intro; exact hy
        rfl
      all_goals exact measurableSet_Icc
    · apply Integrable.indicator; apply Integrable.mul_prod
      · rw [← IntegrableOn]; exact hf
      · rw [← IntegrableOn]; exact hg
      · exact aux_mea
    exact aux_mea
  _ = ∫ (p : ℝ × ℝ) in {p | p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a p.1}, f p.2 * g p.1 ∂(volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc a b)) := by
  -- Apply $Prod.swap$ to the integral on the product space
    set μ := (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc a b))
    have swap_meaP: MeasurePreserving Prod.swap μ μ := Measure.measurePreserving_swap
    have : {p | p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc p.1 b} = Prod.swap '' {p | p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc a p.1} := by
      simp [Set.ext_iff, and_assoc]; intro x y
      constructor; all_goals
      rintro ⟨_,_,_,_⟩; split_ands
      all_goals linarith
    rw [this, swap_meaP.setIntegral_image_emb]; simp
    · let e : Equiv (ℝ × ℝ) (ℝ × ℝ) := {
        toFun := Prod.swap
        invFun := Prod.swap
      }
      let F : MeasurableEquiv (ℝ × ℝ) (ℝ × ℝ) := MeasurableEquiv.mk e (by measurability) (by measurability)
      exact F.measurableEmbedding
  _ = _ := by
  -- Apply Fubini's theorem again to show the integral on the product is equal to the RHS
    symm; nth_rw 2 [← integral_indicator]; rw [integral_prod]
    apply setIntegral_congr_fun; exact measurableSet_Icc
    · intro x hx; simp only
      rw [← integral_indicator, ← integral_indicator]
      apply integral_congr_ae
      · rw [EventuallyEq]; apply ae_of_all
        intro y; rw [Set.indicator_apply]; split_ifs with hy
        · rw [Set.indicator_of_mem, Set.indicator_of_mem]; simp only [Set.mem_setOf_eq]
          exact ⟨hx, hy⟩
          · rw [Set.mem_Icc] at *
            exact ⟨hy.left, by linarith only [hx.right, hy.right]⟩
        rw [Set.indicator_apply]; split_ifs with hy'
        · rw [Set.indicator_of_notMem]; simp only [Set.mem_setOf_eq, not_and]
          intro; exact hy
        rfl
      all_goals exact measurableSet_Icc
    apply Integrable.indicator
    have : (fun p : ℝ × ℝ => f p.2 * g p.1) = fun p => g p.1 * f p.2 := by
      ext; rw [mul_comm]
    rw [this]; apply Integrable.mul_prod
    · rw [← IntegrableOn]; exact hg
    · rw [← IntegrableOn]; exact hf
    all_goals exact aux_mea'

-- Integration-by-parts rule for absolutely continuous functions
theorem absolutelyContinuous_integration_by_parts (f g : ℝ → ℂ) (a b : ℝ) (aleb : a ≤ b) (hg : LocallyIntegrable g volume)
    (df : ∀ x, f x = ∫ t in a..x, g t) : ∀ ψ : ℝ → ℂ, ContDiff ℝ 1 ψ → ∫ t in a..b, f t * deriv ψ t
    = f b * ψ b - ∫ t in a..b, g t * ψ t := by
  intro ψ hψ; rw [df]; simp only [intervalIntegral]
  simp only [show Set.Ioc b a = ∅ by apply Set.Ioc_eq_empty; linarith only [aleb],
    Measure.restrict_empty, integral_zero_measure, sub_zero]
  rw [← integral_mul_const, ← integral_sub, ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  simp only [← mul_sub]; symm; calc
    _ = ∫ (x : ℝ) in Set.Icc a b, g x * ∫ y in Set.Icc x b, deriv ψ y := by
      apply setIntegral_congr_fun; exact measurableSet_Icc
      · intro y hy; simp only [mul_eq_mul_left_iff]; left
        rw [← intervalIntegral.integral_deriv_eq_sub, intervalIntegral]
        have : Set.Ioc b y = ∅ := by
          apply Set.Ioc_eq_empty; rw [Set.mem_Icc] at hy
          linarith only [hy.right]
        simp only [← integral_Icc_eq_integral_Ioc, this, Measure.restrict_empty,
          integral_zero_measure, sub_zero]
        · intros; apply hψ.differentiable; rfl
        · apply Continuous.intervalIntegrable
          apply hψ.continuous_deriv; rfl
    _ = _ := by
      simp only [← integral_const_mul]
      rw [integral_integral_flip]; simp only [integral_mul_const]
      apply setIntegral_congr_fun; exact measurableSet_Icc
      · intro x hx; simp only [mul_eq_mul_right_iff]
        left; rw [df, intervalIntegral]
        have : Set.Ioc x a = ∅ := by
          apply Set.Ioc_eq_empty; rw [Set.mem_Icc] at hx
          push_neg; exact hx.left
        simp only [integral_Icc_eq_integral_Ioc, this, Measure.restrict_empty,
          integral_zero_measure, sub_zero]
      · apply hg.integrableOn_isCompact; exact isCompact_Icc
      · apply Continuous.integrableOn_Icc
        apply hψ.continuous_deriv; rfl
  · apply Integrable.mul_const
    rw [← IntegrableOn, ← integrableOn_Icc_iff_integrableOn_Ioc]
    apply hg.integrableOn_isCompact; exact isCompact_Icc
  · rw [← IntegrableOn, ← integrableOn_Icc_iff_integrableOn_Ioc]
    apply IntegrableOn.mul_continuousOn
    · apply hg.integrableOn_isCompact; exact isCompact_Icc
    apply hψ.continuous.continuousOn; exact isCompact_Icc
