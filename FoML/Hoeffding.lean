import FoML.ForMathlib.Probability.Moments
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF
/-!
# Hoeffding's lemma and Hoeffding's inequality

This file states Hoeffding's lemma and Hoeffding's inequality.

## Main results

* `ProbabilityTheory.hoeffding`: Hoeffding's Lemma states that for a random variable `X` with
  `E[X] = 0` (zero mean) and `a ≤ X ≤ b` almost surely, the inequality
  `mgf X μ t ≤ exp (t^2 * (b - a)^2 / 8)` holds almost surely for all `t ∈ ℝ`.

## References

We follow [martin2019] and [mehryar2018] for the proof of Hoeffding's lemma.
-/

open MeasureTheory ProbabilityTheory Real

namespace ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω := by volume_tac)

theorem cgf_zero_deriv [IsProbabilityMeasure μ] {X : Ω → ℝ} (h0 : μ[X] = 0) :
    let f' := fun t ↦ ∫ (x : Ω), X x ∂Measure.tilted μ fun ω ↦ t * X ω;
  f' 0 = 0 := by
  simp only [zero_mul, tilted_const', measure_univ, inv_one, one_smul]
  exact h0

theorem extracted_1 [IsProbabilityMeasure μ] (t a b : ℝ) {X : Ω → ℝ} (ht : 0 ≤ t) (hX : AEMeasurable X μ)
  (h : ∀ᵐ (ω : Ω) ∂μ, X ω ∈ Set.Icc a b) (h0 : ∫ (x : Ω), X x ∂μ = 0) (w : ¬t = 0) :
  cgf X μ t ≤ t ^ 2 * (b - a) ^ 2 / 8 := by
  let f := fun t ↦ cgf X μ t
  have hf : f 0 = 0 := cgf_zero
  set f' : ℝ → ℝ := fun t ↦ (μ.tilted (fun ω ↦ t * X ω))[X]
  have hf' : f' 0 = 0 := cgf_zero_deriv μ h0
  set f'' : ℝ → ℝ := fun t ↦ variance X (μ.tilted (fun ω ↦ t * X ω))
  have q : ∀ x : ℝ, ∃ c ∈ (Set.Ioo 0 t), f t = f 0 + f' 0 * t + f'' c * t ^ 2 / 2 := by
    let A := (f t - f 0 - f' 0 * t) * 2 / t ^ 2
    have q0 : f t = f 0 + f' 0 * t + A * t ^ 2 / 2 := by
      have q0' : A * t ^ 2 = (f t - f 0 - f' 0 * t) * 2 := by
        calc
        _ = (f t - f 0 - f' 0 * t) * 2 * t ^ 2 / t ^ 2 :=
          Eq.symm (mul_div_right_comm ((f t - f 0 - f' 0 * t) * 2) (t ^ 2) (t ^ 2))
        _ = (f t - f 0 - f' 0 * t) * 2 * (t ^ 2 / t ^ 2) := by ring
        _ = (f t - f 0 - f' 0 * t) * 2 := by field_simp only
      rw [q0']
      ring
    set g : ℝ → ℝ := fun x ↦ f t - f x - f' x * (t - x) - A * (t - x) ^ 2 / 2
    have q1 : g 0 = 0 := by
      dsimp only [g, A]
      calc
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) * 2 / 2 * t ^ 2 / t ^ 2 := by field_simp
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) * 2 / 2 * (t ^ 2 / t ^ 2) := by ring
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) * 2 / 2 := by field_simp
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) := by ring
      _ = 0 := by ring
    have q2 : g t = 0 := by
      dsimp only [g]
      simp only [sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_div]
    set g' : ℝ → ℝ := fun x ↦ - f'' x * (t - x) + A * (t - x)
    have q3 : ∀ x : ℝ, HasDerivAt g (g' x) x := by
      intro x
      apply HasDerivAt.add
      · rw [← (by ring : 0 - f' x + (f' x - f'' x * (t - x)) = - f'' x * (t - x))]
        apply ((hasDerivAt_const x _).sub (cgf_deriv_one a b hX h x)).add
        convert (cgf_deriv_two a b hX h x).mul ((hasDerivAt_id' x).add_const (-t)) using 1
        · ext; ring
        · dsimp [f', f'']
          have p : variance X (Measure.tilted μ fun ω ↦ x * X ω) =
              (μ.tilted fun ω ↦ x * X ω)[X ^ 2] - ((μ.tilted fun ω ↦ x * X ω)[X]) ^ 2 := by
            have _ : IsProbabilityMeasure (μ.tilted fun ω ↦ x * X ω) :=
              isProbabilityMeasure_tilted (integrable_expt_bound hX h)
            have hμ := tilted_absolutelyContinuous μ fun ω ↦ x * X ω
            apply variance_def' <|
              MeasureTheory.memLp_of_bounded (hμ h) (AEMeasurable.aestronglyMeasurable (hX.mono_ac hμ)) 2
          rw [p]
          simp only [Pi.pow_apply, mul_one]
          ring
      · rw [(by ext x; ring : (fun x ↦ -(A * (t - x) ^ 2 / 2)) =
          (fun x ↦ -A * ((x - t) ^ 2 / 2))),
            (by ring : (A * (t - x)) = -A * (x - t))]
        apply HasDerivAt.const_mul
        rw [(by ext x; ring : (fun y ↦ (y - t) ^ 2 / 2) = (fun y ↦ (1 / 2) * (y - t) ^ 2)),
            (by ring : x - t = (1 / 2) * (2 * (x - t)))]
        apply HasDerivAt.const_mul
        rw [(by ext x; ring : (fun y ↦ (y - t) ^ 2) = (fun y ↦ y ^ 2 - 2 * t * y + t ^ 2)),
            (by ring : (2 * (x - t)) = 2 * (x ^ (2 - 1)) - 2 * t + 0)]
        apply HasDerivAt.add
        apply HasDerivAt.add
        apply hasDerivAt_pow
        rw [(by ext x; ring : (fun x ↦ -(2 * t * x)) = (fun x ↦ (x * -(2 * t))))]
        apply hasDerivAt_mul_const
        apply hasDerivAt_const
    have q4 : ∃ c ∈ (Set.Ioo 0 t), g' c = 0 := by
      apply exists_hasDerivAt_eq_zero (lt_of_le_of_ne ht fun a ↦ w (a.symm))
      apply HasDerivAt.continuousOn
      intros x _; exact q3 x
      rw [q1, q2]
      intros x _; exact q3 x
    obtain ⟨c, ⟨cq, cq'⟩⟩ := q4
    intro
    use c; constructor
    · exact cq
    · dsimp only [g'] at cq';
      have cq'' : (A - f'' c) * (t - c) = 0 := by linarith
      have cq''' : A = f'' c := by
        have cr : (A - f'' c) = 0 := by
          simp only [mul_eq_zero] at cq''
          obtain cq''' | cq'''' := cq''
          · exact cq'''
          · dsimp only [Set.Ioo] at cq
            obtain ⟨_, cq2⟩ := cq
            linarith
        linarith
      rw [← cq''']
      exact q0
  rw [hf, hf'] at q
  simp only [Set.mem_Ioo, zero_mul, add_zero, zero_add, forall_const] at q
  obtain ⟨c, ⟨_, cq'⟩⟩ := q
  have s : f t ≤ t^2 * (b - a)^2 / 8 := by
    rw [cq']
    calc
    _ ≤ ((b - a) / 2) ^ 2 * t ^ 2 / 2 := by
      apply mul_le_mul_of_nonneg_right
      apply mul_le_mul_of_nonneg_right
      dsimp [f'']
      have _ : IsProbabilityMeasure (μ.tilted fun ω ↦ t * X ω) :=
        isProbabilityMeasure_tilted (integrable_expt_bound hX h)
      exact tilt_var_bound a b c h hX
      exact sq_nonneg t; simp only [inv_nonneg, Nat.ofNat_nonneg]
    _ = t ^ 2 * (b - a) ^ 2 / 8 := by ring
  exact s

/-! ### Hoeffding's lemma restricted to t ≥ 0-/

theorem hoeffding_nonneg [IsProbabilityMeasure μ]
    (t a b : ℝ) {X : Ω → ℝ} (ht : 0 ≤ t) (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (h0 : μ[X] = 0) :
    mgf X μ t ≤ exp (t^2 * (b - a)^2 / 8) := by
  dsimp [mgf]
  by_cases w : t = 0;
    · rw [w]; simp only [zero_mul, exp_zero, integral_const, measure_univ,
    ENNReal.one_toReal, smul_eq_mul, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, le_refl]
  set f : ℝ → ℝ := fun t ↦ cgf X μ t
  suffices f t ≤ t^2 * (b - a)^2 / 8 from by
    rw [<- log_le_iff_le_exp]
    exact this
    apply mgf_pos' (Ne.symm (NeZero.ne' μ))
    apply integrable_expt_bound hX h
  exact ProbabilityTheory.extracted_1 μ t a b ht hX h h0 w

/-! ### Hoeffding's lemma-/

/-- Hoeffding's Lemma states that for a random variable `X` with `E[X] = 0` (zero mean) and
 `a ≤ X ≤ b` almost surely, the inequality
 `μ[exp (t * (X ω))] ≤ exp (t^2 * (b - a)^2 / 8)` holds almost surely for all `t ∈ ℝ`.-/
theorem hoeffding [IsProbabilityMeasure μ] (t a b : ℝ) {X : Ω → ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (h0 : μ[X] = 0) :
    mgf X μ t ≤ exp (t^2 * (b - a)^2 / 8) := by
  by_cases h' : 0 ≤ t
  case pos =>
    exact hoeffding_nonneg μ t a b h' hX h h0
  case neg =>
    simp only [not_le] at h'
    suffices ∫ ω, rexp (- t * - X ω) ∂μ ≤
      rexp ((- t) ^ 2 * ((- a) - (- b)) ^ 2 / 8) from by
      simp only [mul_neg, neg_mul, neg_neg, even_two, Even.neg_pow, sub_neg_eq_add] at this
      rw [<- (by ring : (-a + b) = b - a)]
      exact this
    apply hoeffding_nonneg _ _ _ _ (by linarith : 0 ≤ - t) hX.neg
    · simp only [Set.mem_Icc, neg_le_neg_iff, Filter.eventually_and]
      exact ⟨h.mono fun ω h ↦ h.2, h.mono fun ω h ↦ h.1⟩
    · rw [integral_neg]
      simp only [neg_eq_zero]
      exact h0


lemma min_exp_bound (ε a b:ℝ)(m:ℕ)(hm : m > 0)(hε : ε > 0) (hab : b > a):
  (⨅ t : {t : ℝ // t > 0}, exp (-t*ε + t^2 * (m:ℝ) * (b - a)^2 / 8)) = exp (-2*ε^2 / ((b - a)^2 * m)) := by
  let g : {t : ℝ // t>0} → ℝ := fun t => -t * ε + t^2 * m * (b - a)^2 / 8

  let t_min: {t : ℝ // t>0} := ⟨4 * ε / ((b - a)^2*m), by
    apply div_pos
    · apply mul_pos
      · norm_num
      · exact hε
    · apply mul_pos
      · exact sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr hab))
      · exact Nat.cast_pos.mpr hm
⟩
  have gt: ∀ t :{t : ℝ // t>0}, g t =-t * ε + t^2 * m * (b - a)^2 / 8:= by
    intro t
    simp only [g]
  have h_rewrite : ∀ (t : {t : ℝ // t>0}),
    g t = (m * (b - a)^2 / 8) * (t - t_min)^2 - 2 * ε^2 / ((b - a)^2 * (m : ℝ)) := by
    intro t
    simp only [g, t_min]
    field_simp [ne_of_gt (sub_pos.mpr hab), Nat.cast_ne_zero.mpr (ne_of_gt hm)]
    ring
  have h_inf : ∀(t : {t : ℝ // t>0}), g t ≥ g t_min := by
    intro t
    rw [h_rewrite t, h_rewrite t_min]
    simp only [sub_self, mul_zero]
    have h_term_nonneg : ↑m * (b - a) ^ 2 / 8 * (t - t_min) ^ 2 ≥ 0 := by
      apply mul_nonneg
      · apply div_nonneg
        · apply mul_nonneg
          · exact Nat.cast_nonneg m
          · exact sq_nonneg (b - a)
        · norm_num
      · exact sq_nonneg (t.val - t_min)
    linarith
  have h_exp : ∀ (t : {t : ℝ // t>0}), exp (g t) ≥ exp (g t_min) := fun t ↦ by
    apply exp_le_exp.mpr (h_inf t)

  have h_g_tmin : g t_min = -2 * ε^2 / ((b - a)^2 * (m : ℝ)) := by
    simp only [g, t_min]
    have h : m ≠ 0 ∧ (b - a) ≠ 0:= by
      constructor
      · exact ne_of_gt  hm
      · exact ne_of_gt (sub_pos.mpr hab)
    field_simp [h.left, h.right]
    ring
  have h_exp_tmin : exp (g t_min) = exp (-2 * ε^2 / ((b - a)^2 * (m : ℝ))) := by
    rw [h_g_tmin]
  rw [← h_exp_tmin]

  have h_inf_rewrite : ⨅ t : {t : ℝ // t>0}, rexp (-t * ε + t ^ 2 * ↑m * (b - a) ^ 2 / 8) = ⨅ t : {t : ℝ // 0 < t}, rexp (g t) := by
    congr

  rw [h_inf_rewrite]
  have inf_eq_at_min (g : {t : ℝ // t>0} →ℝ ) (t_min : {t : ℝ // t>0}) (h_exp : ∀ t : {t : ℝ // t>0}, rexp (g t) ≥ rexp (g t_min)) :
    ⨅ t:{t : ℝ // t>0}, rexp (g t) = rexp (g t_min) := by

    apply le_antisymm
    · have bdd : BddBelow (Set.range (fun t => rexp (g t))) := by
        use rexp (g t_min)
        intro y hy
        rcases hy with ⟨t, rfl⟩
        exact h_exp t

      apply ciInf_le bdd
    · have positive_reals_nonempty : Nonempty {t : ℝ // t > 0} := by
        exact ⟨⟨1, by norm_num⟩⟩
      apply le_ciInf
      intro t
      exact (h_exp t)
  exact inf_eq_at_min g t_min h_exp

/-- Hoeffding's inequality states that for m independent random variables X₁,...,Xₘ where each Xᵢ is bounded in [a,b] almost surely,
the probability that their empirical mean deviates from its expected value by more than ε is bounded by:

P(∑ᵢXᵢ - E[∑ᵢXᵢ] ≥ ε) ≤ exp(-2ε²/m(b-a)²)
-/
theorem hoeffding_inequality [IsProbabilityMeasure μ] (a b : ℝ) {m : ℕ} {X : Fin m → Ω → ℝ} (hXm : ∀ i: Fin m, Measurable (X i)) (hXi : iIndepFun X μ) (hab : b > a) (h : ∀ i: Fin m, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b) (ε : ℝ)(hm:m>0) (hε : ε > 0) : (μ {ω | ε ≤ (∑ i, X i ω - μ[fun ω : Ω ↦ ∑ i, X i ω])}).toReal ≤ exp (- 2* ε^2 /((b - a)^2 * (m : ℝ))) := by
  let Y : Fin m → Ω → ℝ := fun i ↦ (fun ω ↦ X i ω - μ[fun ω : Ω ↦ X i ω])

  -- X i is integrable
  have hXint : ∀ i : Fin m, Integrable (X i) μ := by
    intro i
    let C := max (|a|) (|b|)
    have h_bdd : ∀ᵐ ω ∂μ, |X i ω| ≤ C := by
      filter_upwards [h i] with ω hω
      exact abs_le_max_abs_abs hω.1 hω.2
    have h_int_C : Integrable (fun _ => C) μ := by
      apply MeasureTheory.integrable_const
    -- have h_ae_strong : AEStronglyMeasurable (fun x ↦ |X i x|) μ := by
    --   apply AEMeasurable.aestronglyMeasurable (hXm i).abs
    apply Integrable.mono' h_int_C (hXm i).aestronglyMeasurable
    filter_upwards [h_bdd] with ω hω
    exact hω


  -- Y i is bounded by a - μ[X i] and b - μ[X i]
  have hY_b : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (a - μ[X i]) (b - μ[X i]) := by
    intro i
    filter_upwards [h i] with ω hω
    simp only [Y, Set.mem_Icc]
    constructor
    · exact sub_le_sub_right hω.1 (μ[X i])
    · exact sub_le_sub_right hω.2 (μ[X i])

  have hYmeas_ae : ∀ i : Fin m, AEMeasurable (Y i) μ := by
    intro i
    exact AEMeasurable.sub (Measurable.aemeasurable (hXm i)) aemeasurable_const
  have hYmeas : ∀ i : Fin m, Measurable (Y i):= by
    intro i
    exact Measurable.sub (hXm i) (measurable_const)
  have h_hoeffding_bound: ∀ t : ℝ, ∀ i, mgf (Y i) μ t ≤ exp (t^2 * (b - a)^2 / 8) := by
    -- `E[Y i] = 0`
    have hY: ∀ i, μ[Y i]= 0 := by
      intro i
      simp only [Y]
      let constFn : Ω → ℝ := fun _ ↦ ∫ ω, X i ω ∂μ
      have h_const_int : Integrable constFn μ := by
        exact integrable_const _

      have h_int_sub : ∫ x, (X i x - constFn x) ∂μ
                  = ∫ x, X i x ∂μ - ∫ x, constFn x ∂μ := by
        exact integral_sub (hXint i) h_const_int

      have h_const_eval : ∫ x, constFn x ∂μ = ∫ x, X i x ∂μ := by
        rw [integral_const]
        simp
      rw [h_int_sub, h_const_eval]
      exact sub_self _
    intros t i
    have h_bounds_eq : (b - μ[X i]) - (a - μ[X i]) = b - a := by ring
    have h_bound := hoeffding μ t (a - μ[X i]) (b - μ[X i]) (hYmeas_ae i) (hY_b i) (hY i)
    rw [h_bounds_eq] at h_bound
    exact h_bound

  have h_ysum: {ω | ε ≤ ∑ i, Y i ω} = {ω | ε ≤ ∑ i, X i ω - μ[fun ω : Ω ↦ ∑ i, X i ω]} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have h_sum_eq : ∑ i, Y i ω = ∑ i, X i ω - μ[fun ω ↦ ∑ i, X i ω] := by
      have h_expand : ∑ i, Y i ω = ∑ i, (X i ω - ∫ (x : Ω), X i x ∂μ) := by
        simp only [Y]
      have h_distrib : ∑ i, (X i ω - ∫ (x : Ω), X i x ∂μ) = ∑ i, X i ω - ∑ i, ∫ (x : Ω), X i x ∂μ := by
        apply Finset.sum_sub_distrib
      have h_int_sum : ∑ i, ∫ (x : Ω), X i x ∂μ = ∫ (x : Ω), ∑ i, X i x ∂μ := by
        rw [integral_finset_sum]
        intro j _
        exact hXint j
      calc ∑ i, Y i ω
        = ∑ i, (X i ω - ∫ (x : Ω), X i x ∂μ) := h_expand
        _ = ∑ i, X i ω - ∑ i, ∫ (x : Ω), X i x ∂μ := h_distrib
        _ = ∑ i, X i ω - ∫ (x : Ω), ∑ i, X i x ∂μ := by rw [h_int_sum]
    rw [h_sum_eq]
  rw [ ←h_ysum]

  have h_ysum_mgf: ∀ t:ℝ, mgf (fun ω ↦ ∑ i, Y i ω) μ t = ∏ i, mgf (Y i) μ t := by
    intro t
    have h_Y_indep : iIndepFun Y μ := by
      let g :=  fun i ↦ (fun (xx: ℝ) ↦(xx- μ[fun ω : Ω ↦ X i ω]))
      have this:  Y = (fun i ↦ (g i ∘ X i) ) := by
        ext i ω
        simp only [Function.comp_apply, Y, g]
      rw [this]
      have h_g_measure:∀ i, Measurable (g i) := by
        intro i
        exact Measurable.sub (measurable_id' ) (measurable_const)
      exact iIndepFun.comp hXi g h_g_measure

    rw [← iIndepFun.mgf_sum h_Y_indep hYmeas Finset.univ]
    congr with x
    rw [Finset.sum_apply]
  have h_markov (t:ℝ) (ht: t>0) : (μ {ω | exp (t * ε) ≤ exp (t * ∑ i, Y i ω)}).toReal ≤ μ[fun ω : Ω ↦ exp (t * ∑ i, Y i ω)] /exp (t * ε)  := by

    have h_mgf_sum_int : Integrable (fun ω ↦ exp (t * ∑ i, Y i ω)) μ := by
      have sum_y_b:  ∀ᵐ ω ∂μ, exp (t * ∑ i, Y i ω) ∈ Set.Icc (exp (t* ∑ i, (a - μ[X i]))) (exp (t* ∑ i, (b - μ[X i]))):= by
        simp only [Y, Set.mem_Icc]
        field_simp
        have h₀ : ∀ᵐ ω ∂μ, ∀ i, X i ω ∈ Set.Icc a b := ae_all_iff.mpr h
        constructor
        · filter_upwards [h₀] with ω hω
          calc
            ↑m * a = ∑ _i : Fin m, a := by simp [nsmul_eq_mul]
            _ ≤ ∑ x : Fin m, X x ω := by exact Finset.sum_le_sum fun i _ => (hω i).1
        · filter_upwards [h₀] with ω hω
          calc
            ∑ x : Fin m, X x ω ≤  ∑ x : Fin m, b := by exact Finset.sum_le_sum fun i _ => (hω i).2
            _ = ↑m * b := by simp [nsmul_eq_mul]
      have h_int_C : Integrable (fun _ => exp (t* ∑ i, (b - μ[X i]))) μ := by  apply MeasureTheory.integrable_const

      have exp_sum_aemeasurable : AEStronglyMeasurable (fun ω ↦ exp (t * ∑ i, Y i ω)) μ := by
        have sum_measurable : Measurable (fun ω ↦ ∑ i, Y i ω):= by
          apply Finset.measurable_sum
          intro i _
          exact hYmeas i
        have mul_measurable : Measurable (fun ω ↦ t * ∑ i, Y i ω)  :=
          Measurable.const_mul sum_measurable t
        exact AEMeasurable.aestronglyMeasurable (Measurable.aemeasurable (Measurable.exp mul_measurable))
      apply Integrable.mono' h_int_C exp_sum_aemeasurable
      filter_upwards [sum_y_b] with ω hω
      revert hω
      field_simp
    have h_mgf_sum_meas :0 ≤ᶠ[ae μ] fun ω ↦ Real.exp (t * ∑ i, Y i ω)  := by
      filter_upwards with ω
      exact le_of_lt (exp_pos (t * ∑ i, Y i ω))
    have this: rexp (t * ε) * (μ {ω | exp (t * ε) ≤ exp (t * ∑ i, Y i ω)}).toReal ≤ μ[fun ω : Ω ↦ exp (t * ∑ i, Y i ω)] := by
      exact MeasureTheory.mul_meas_ge_le_integral_of_nonneg h_mgf_sum_meas h_mgf_sum_int (exp (t * ε))
    rw [div_eq_inv_mul]
    apply (mul_le_mul_right (Real.exp_pos (t*ε))).mp
    rw [mul_comm]
    revert this
    field_simp

  have h_t_bound (t:ℝ) (ht: t>0):(μ {ω | ε ≤ ∑ i : Fin m, Y i ω}).toReal ≤ exp (-t*ε+ t^2 *(m:ℝ)*(b - a)^2 / 8) := by
    have h_mu_exp_equal(t:ℝ) (ht: t>0) : (μ {ω | ε ≤ ∑ i, Y i ω}).toReal= (μ {ω | exp (t * ε) ≤ exp (t * ∑ i, Y i ω)}).toReal := by field_simp
    rw [h_mu_exp_equal t ht]
    apply le_trans (h_markov t ht)
    simp [mgf] at h_ysum_mgf
    simp [mgf] at h_hoeffding_bound
    rw [h_ysum_mgf t]

    have this: (∏ i : Fin m, μ[fun ω : Ω ↦ exp (t * Y i ω)]) / exp (t * ε)
      ≤ (∏ i : Fin m, exp (t ^ 2 * (b - a) ^ 2 / 8)) / exp (t * ε) := by
        rw [div_eq_mul_inv,div_eq_mul_inv,mul_comm]
        nth_rewrite 3 [mul_comm]
        apply (mul_le_mul_left (inv_pos_of_pos (exp_pos (t * ε)))).mpr
        apply Finset.prod_le_prod
        · field_simp
          intro i
          apply integral_nonneg
          intro a
          exact (exp_pos _).le
        · field_simp
          intro i
          exact h_hoeffding_bound t i

    rw [Finset.prod_const,Finset.card_fin,← exp_nat_mul,← exp_sub] at this
    ring_nf at this
    ring_nf
    exact this
  rw [← min_exp_bound ε a b m hm hε hab]
  have positive_reals_nonempty : Nonempty {t : ℝ // t > 0} := by
    exact ⟨⟨1, by norm_num⟩⟩
  apply le_ciInf
  intro t
  exact h_t_bound t t.property


end ProbabilityTheory
