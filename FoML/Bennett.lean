import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Variance
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Filter
import FoML.Hoeffding

open scoped Topology
open MeasureTheory ProbabilityTheory BigOperators ENNReal Real Set Filter Asymptotics

universe u

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {n : ℕ} {X : Fin n → Ω → ℝ}
def S := fun ω ↦ ∑ i, X i ω

noncomputable def bennett_h (u : ℝ) : ℝ := (1 + u) * log (1 + u) - u

lemma exp_bound (x τ : ℝ) (hx :|x| ≤ 1) (hτ : 0 ≤ τ) :
    rexp (τ * x) ≤ 1 + τ * x + x ^ 2 * ((rexp τ) - 1 - τ) := by
  have hx_le_1 : x ≤ 1 := by
    rw [abs_le] at hx
    exact hx.2
  apply le_of_sub_nonpos
  set f : ℝ → ℝ := fun τ =>
    rexp (τ * x) - (1 + τ * x + x ^ 2 * (rexp τ - 1 - τ))
  set f' : ℝ → ℝ := fun τ =>
    rexp (τ * x) * x - (x + x ^ 2 * (rexp τ - 1))
  set f'' : ℝ → ℝ := fun τ =>
    rexp (τ * x) * x * x - x ^ 2 * rexp τ
  change f τ ≤ 0
  have hf0 : f 0 = 0 := by simp [f]
  have hf'0 : f' 0 = 0 := by simp [f']
  rw [← hf0]
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (by fun_prop)
    (fun t _ => ((hasDerivAt_mul_const x).exp.sub
      (((hasDerivAt_mul_const x).const_add 1).add
        ((((hasDerivAt_exp t).sub_const 1).sub (hasDerivAt_id t)).const_mul
          (x ^ 2)))).hasDerivWithinAt)
    (fun t ht => ?_) left_mem_Ici hτ hτ
  show f' t ≤ 0
  rw [← hf'0]
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (by fun_prop)
    (fun t _ => (((hasDerivAt_mul_const x).exp.mul_const x).sub
      ((((hasDerivAt_exp t).sub_const 1).const_mul (x ^ 2)).const_add x)).hasDerivWithinAt)
    (fun u hu => ?_) left_mem_Ici (interior_subset ht) (interior_subset ht)
  apply sub_nonpos_of_le
  rw [mul_assoc, ← sq, mul_comm (rexp _)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg x)
  apply exp_monotone
  refine (mul_le_iff_le_one_right ?_).mpr hx_le_1
  rwa [interior_Ici] at hu

theorem sum_integrable {Ω : Type u} [inst : MeasurableSpace Ω] (μ : Measure Ω) [inst_1 : IsProbabilityMeasure μ]
  {n : ℕ} {X : Fin n → Ω → ℝ} (hXm : ∀ (i : Fin n), Measurable (X i))
  (hX_bdd : ∀ (i : Fin n), ∀ᵐ (ω : Ω) ∂μ, |X i ω| ≤ 1) (τ : ℝ) (hlam : τ ≥ 0) :
  Integrable (fun ω ↦ rexp (τ * ∑ i, X i ω)) μ := by
  let S := fun ω ↦ ∑ i, X i ω
  have hS_meas : Measurable S := by
    unfold S
    let I : Finset (Fin n) := Finset.univ
    have hXm' : ∀ i ∈ I, Measurable (X i) := by
      intro i hi
      exact hXm i
    have h := Finset.measurable_sum (s := I) (hf := hXm')
    exact h
  have h_exp_prod : Integrable (fun ω ↦ rexp (τ * S ω)) μ := by
    let f : ℝ → ℝ := fun x ↦ rexp (τ * x)
      -- Prove it's measurable
    have f_meas : Measurable f := measurable_exp.comp (measurable_id.const_mul (τ))
    have f_measω : Measurable fun ω ↦ rexp (τ * S ω) := f_meas.comp hS_meas
    constructor
    · exact f_measω.aestronglyMeasurable
    · have h_bound : ∀ i, ∀ᵐ ω ∂μ, ‖rexp (τ * X i ω)‖ ≤ rexp (τ) := by
        intro i
        filter_upwards [hX_bdd i] with ω hω
        rw [norm_eq_abs, abs_of_nonneg (exp_pos _).le]
        rw [exp_le_exp]
        have h := mul_le_mul_of_nonneg_left (abs_le.mp hω).2 (hlam)
        linarith [h]
      have h_sum_bound : ∀ᵐ ω ∂μ, ‖rexp (τ * S ω)‖ ≤ rexp (n * τ) := by
        have h_all : ∀ᵐ (ω : Ω) ∂μ, ∀ i, |X i ω| ≤ 1 := by
          rw [ae_all_iff]
          exact hX_bdd
        filter_upwards [h_all] with ω hω
        rw [norm_eq_abs, abs_of_nonneg (exp_pos _).le]
        rw [exp_le_exp]
        suffices S ω ≤ n by nlinarith
        unfold S
        calc
          ∑ i, X i ω ≤ ∑ i, |X i ω| := by gcongr; exact le_abs_self (X _ ω)
          _ ≤ ∑ i, 1 := by gcongr; exact hω _
          _ = n := by simp [Finset.sum_const, nsmul_eq_mul, mul_one]
      apply HasFiniteIntegral.mono' (g := fun _ ↦ Real.exp (↑n * τ))
      · simp only [HasFiniteIntegral]
        rw [lintegral_const]
        simp [mul_eq_top, ENNReal.ofReal_lt_top]
      · exact h_sum_bound
  unfold S at h_exp_prod
  exact h_exp_prod

theorem single_integrable1 {Ω : Type u_1} [inst : MeasurableSpace Ω] (μ : Measure Ω) [inst_1 : IsProbabilityMeasure μ]
  {n : ℕ} {X : Fin n → Ω → ℝ} (hXm : ∀ (i : Fin n), Measurable (X i))
  (hX_bdd : ∀ (i : Fin n), ∀ᵐ (ω : Ω) ∂μ, |X i ω| ≤ 1) (τ : ℝ) (hlam : τ ≥ 0) :
  ∀ (i : Fin n), Integrable (fun ω ↦ rexp (τ * X i ω)) μ := by
  intro i
  have hbdd : ∀ᵐ ω ∂μ, rexp (τ * X i ω) ∈ Set.Icc (rexp (-τ)) (rexp (τ)) := by
    filter_upwards [hX_bdd i] with ω hω
    have : X i ω ∈ Set.Icc (-1) 1 := by rw [Set.mem_Icc]; exact abs_le.mp hω
    simp only [Set.mem_Icc] at this
    constructor
    · apply Real.exp_le_exp.mpr
      rw [mul_comm]
      have h := mul_le_mul_of_nonneg_left this.1 (hlam)
      linarith [h]
    · apply Real.exp_le_exp.mpr
      rw [mul_comm]
      have h := mul_le_mul_of_nonneg_left this.2 (hlam)
      linarith [h]
  constructor
  · measurability
  · have h_bound : ∀ᵐ ω ∂μ, ‖rexp (τ * X i ω)‖ ≤ rexp (τ) := by
      filter_upwards [hbdd] with ω hω
      rw [norm_eq_abs, abs_of_nonneg (exp_pos _).le]
      exact hω.2
    exact hasFiniteIntegral_of_bounded h_bound

theorem single_integrable2 {Ω : Type u_1} [inst : MeasurableSpace Ω] (μ : Measure Ω) [inst_1 : IsProbabilityMeasure μ]
  {n : ℕ} {X : Fin n → Ω → ℝ} (hXm : ∀ (i : Fin n), Measurable (X i))
  (hX_bdd : ∀ (i : Fin n), ∀ᵐ (ω : Ω) ∂μ, |X i ω| ≤ 1) (τ : ℝ) :
  ∀ i, Integrable (fun ω ↦ 1 + τ * X i ω + X i ω ^ 2 * (rexp τ - 1 - τ)) μ := by
  intro i
  constructor
  · have h1 : AEStronglyMeasurable (fun _ ↦ (1 : ℝ)) μ := aestronglyMeasurable_const
    have h2 : AEStronglyMeasurable (fun ω ↦ τ * X i ω) μ := (aestronglyMeasurable_const.mul (Measurable.aestronglyMeasurable (hXm i)))
    have h3 : AEStronglyMeasurable (fun ω ↦ (X i ω)^2) μ := (Measurable.pow (hXm i) (by measurability)).aestronglyMeasurable
    have h4 : AEStronglyMeasurable (fun ω ↦ (X i ω)^2 * (Real.exp τ - 1 - τ)) μ := h3.mul aestronglyMeasurable_const
    have h5 := h1.add (h2.add h4)
    have : (fun ω ↦ 1 + τ * X i ω + X i ω ^ 2 * (Real.exp τ - 1 - τ)) =
      (fun ω ↦ 1) + ((fun ω ↦ τ * X i ω) + (fun ω ↦ X i ω ^ 2 * (Real.exp τ - 1 - τ))) := by
      ext ω
      simp only [Pi.add_apply, add_assoc]
    rw [this]
    exact h5
  · have h1 : Integrable (fun ω ↦ 1 + τ * X i ω) (μ := μ) := by
      have h_const : Integrable (fun _ ↦ (1 : ℝ)) μ :=
        integrable_const 1
      have h_mul : Integrable (fun ω ↦ τ * X i ω) μ := by
        have hX_int : Integrable (fun ω ↦ X i ω) μ := by
          constructor
          · exact (hXm i).aestronglyMeasurable
          · have h_bound : ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ 1 := by
              filter_upwards [hX_bdd i] with ω hω
              exact hω
            apply hasFiniteIntegral_of_bounded (C := 1)
            exact h_bound
        have h_mul' := Integrable.const_mul hX_int τ
        exact h_mul'
      have := Integrable.add' h_const h_mul
      simp [<-Pi.add_apply]
      exact h_mul
    have h2 : Integrable (fun ω ↦ X i ω ^ 2 * (Real.exp τ - 1 - τ)) (μ := μ) := by
      have h_int : Integrable (fun ω ↦ X i ω ^ 2) μ := by
        constructor
        · exact (Measurable.pow (hXm i) (by measurability)).aestronglyMeasurable
        · have h_bound : ∀ᵐ a ∂μ, X i a ^ 2 ≤ 1 := by
            filter_upwards [hX_bdd i] with a ha
            rw [sq_le_one_iff_abs_le_one]
            exact ha
          have h_lbound : ∀ᵐ a ∂μ, X i a ^ 2 ≥ 0 := by
            filter_upwards [hX_bdd i] with a ha
            positivity
          have h_box : ∀ᵐ a ∂μ, X i a ^ 2 ∈ Set.Icc 0 1 := by
            filter_upwards [h_bound, h_lbound] with a ha hlb
            simp only [Set.mem_Icc]
            constructor
            · exact hlb
            · exact ha
          apply HasFiniteIntegral.of_mem_Icc (a := 0) (b := 1) h_box
      apply Integrable.mul_const h_int (rexp τ - 1 - τ)
    have h3 := Integrable.add' h1 h2
    have : (fun ω ↦ 1 + τ * X i ω + X i ω ^ 2 * (Real.exp τ - 1 - τ)) =
      (fun ω ↦ 1 + τ * X i ω) + (fun ω ↦ X i ω ^ 2 * (Real.exp τ - 1 - τ)) := by
      ext ω
      simp only [Pi.add_apply, add_assoc]
    rw [this]
    exact h3

theorem bennett_bound1
    {n : ℕ}
    {X : Fin n → Ω → ℝ}
    (σ : ℝ)
    (ε : ℝ) :
    ∀ τ ≥ 0, Integrable (fun ω ↦ rexp (τ * ∑ i, X i ω)) μ → (μ {ω | ε ≤ ∑ i, X i ω}).toReal ≤ rexp (-τ * ε) * mgf (fun ω ↦ ∑ i, X i ω) μ τ := by
  intro τ hτ
  let S := fun ω => ∑ i, X i ω
  have ht_sq : 0 ≤ σ^2 := by positivity
  have chernoff_bound := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := μ) (t := τ) (ε := ε) (X := S) (ht := hτ)
  exact chernoff_bound

theorem bennett_bound
    {n : ℕ}
    {X : Fin n → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ)
    (hX_bdd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hμX : ∀ i, μ[X i] = 0)
    (σ : ℝ)
    (hσ : ∀ i, σ ^ 2 = μ[X i^2])
    (ε : ℝ) :
    ∀ τ ≥ 0, (μ {ω | ε ≤ ∑ i, X i ω}).toReal ≤ rexp (-(τ * ε) + n * σ ^ 2 * (rexp τ - 1 - τ)) := by
    intro τ hτ
    have chernoff_bound := bennett_bound1 (μ := μ) (n:=n) (X:=X) (σ:=σ) (ε:=ε) (τ:=τ)
    have h_chernoff := chernoff_bound hτ
    have h_integ : Integrable (fun ω ↦ rexp (τ * ∑ i, X i ω)) μ := by
      exact sum_integrable μ hXm hX_bdd τ hτ
    have h_ysum_mgf: ∀ t, mgf (fun ω ↦ ∑ i, X i ω) μ t = ∏ i, mgf (X i) μ t := by
      intro t
      have hXmeas : ∀ i : Fin n, Measurable (X i):= by
        intro i
        exact hXm i
      rw [← iIndepFun.mgf_sum hXi hXmeas Finset.univ]
      congr with x
      rw [Finset.sum_apply]
    rw [h_ysum_mgf] at chernoff_bound
    simp [hτ, h_integ] at chernoff_bound
    suffices rexp (-(τ * ε)) * ∏ i, mgf (X i) μ τ ≤ rexp (-(τ * ε) + n * σ ^ 2 * (rexp τ - 1 - τ)) by linarith
    unfold mgf
    simp only
    have h_single : ∏ i, ∫ (ω : Ω), rexp (τ * X i ω) ∂μ ≤ rexp (n * σ^2 * (rexp (τ) - 1 - τ)) := by
      have this : ∀ i, ∫ (ω : Ω), rexp (τ * X i ω) ∂μ ≤ rexp (σ^2 * (rexp (τ) - 1 - τ)) := by
        have h_exp_taylor : ∀ i, ∀ᵐ ω ∂μ, rexp (τ * X i ω) ≤ 1 + τ * X i ω + (X i ω) ^ 2 * (rexp (τ) - 1 - τ) := by
          intro i
          filter_upwards [hX_bdd i] with ω hω
          let x := X i ω
          have h_x_abs_le_1 : |x| ≤ 1 := by
            unfold x
            exact hω
          have h_exp_bound : rexp (τ * x) ≤ 1 + τ * x + (x) ^ 2 * (rexp (τ) - 1 - τ) := by
            exact exp_bound x τ h_x_abs_le_1 hτ
          simp only [h_x_abs_le_1, hτ] at h_exp_bound
          unfold x at h_exp_bound
          exact h_exp_bound
        intro i
        have h_single_integ1 : Integrable (f := fun ω => rexp (τ * X i ω)) (μ := μ) := by
          exact single_integrable1 μ hXm hX_bdd τ hτ i
        have h_single_integ2 : Integrable (f := fun ω => 1 + τ * X i ω + (X i ω) ^ 2 * (rexp (τ) - 1 - τ)) (μ := μ) := by
          exact single_integrable2 μ hXm hX_bdd τ i
        have h_exp_int : ∫ (ω : Ω), rexp (τ * X i ω) ∂μ ≤ ∫ (ω : Ω), 1 + τ * X i ω + (X i ω) ^ 2 * (rexp (τ) - 1 - τ) ∂μ := by
          apply integral_mono_ae h_single_integ1 h_single_integ2
          exact h_exp_taylor i
        have h_int_decomp : ∫ (ω : Ω), 1 + τ * X i ω + X i ω ^ 2 * (rexp τ - 1 - τ) ∂μ =
          (∫ (ω : Ω), 1 ∂μ) + (∫ (ω : Ω), τ * X i ω ∂μ) + (∫ (ω : Ω), X i ω ^ 2 * (rexp τ - 1 - τ) ∂μ) := by
          have h_const : Integrable (fun _ ↦ (1 : ℝ)) μ :=
            integrable_const 1
          have hX_int : Integrable (fun ω ↦ X i ω) μ := by
            constructor
            · exact (hXm i).aestronglyMeasurable
            · have h_bound : ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ 1 := by
                filter_upwards [hX_bdd i] with ω hω
                exact hω
              apply hasFiniteIntegral_of_bounded (C := 1)
              exact h_bound
          have h_mul' := Integrable.const_mul hX_int τ
          have := Integrable.add' h_const h_mul'
          rw [integral_add]; rw [integral_add]
          simp only [h_const]
          simp only [h_mul']
          simp [<-Pi.add_apply]
          simp only [h_mul']
          have h_int : Integrable (fun ω ↦ X i ω ^ 2) μ := by
            constructor
            · exact (Measurable.pow (hXm i) (by measurability)).aestronglyMeasurable
            · have h_bound : ∀ᵐ a ∂μ, X i a ^ 2 ≤ 1 := by
                filter_upwards [hX_bdd i] with a ha
                rw [sq_le_one_iff_abs_le_one]
                exact ha
              have h_lbound : ∀ᵐ a ∂μ, X i a ^ 2 ≥ 0 := by
                filter_upwards [hX_bdd i] with a ha
                positivity
              have h_box : ∀ᵐ a ∂μ, X i a ^ 2 ∈ Set.Icc 0 1 := by
                filter_upwards [h_bound, h_lbound] with a ha hlb
                simp only [Set.mem_Icc]
                constructor
                · exact hlb
                · exact ha
              apply HasFiniteIntegral.of_mem_Icc (a := 0) (b := 1) h_box
          have h_mul'' := Integrable.mul_const h_int (rexp τ - 1 - τ)
          exact h_mul''
        have h_tmp : ∫ (ω : Ω), τ * X i ω ∂μ = τ * (∫ (ω : Ω), X i ω ∂μ) := by
          rw [integral_mul_left]
        rw [h_tmp] at h_int_decomp
        rw [hμX i] at h_int_decomp
        simp only [mul_zero, add_zero] at h_int_decomp
        rw [h_int_decomp] at h_exp_int
        suffices ∫ (ω : Ω), 1 ∂μ + ∫ (ω : Ω), X i ω ^ 2 * (rexp τ - 1 - τ) ∂μ ≤ rexp (σ ^ 2 * (rexp τ - 1 - τ)) by linarith
        have hmu : ∫ (ω : Ω), (1 : ℝ) ∂μ = 1 := by
          simp [ENNReal.ofReal_mul, norm_eq_abs, abs_sq]
        rw [hmu, integral_mul_right, add_comm]
        have hmu2 : (∫ (a : Ω), X i a ^ 2 ∂μ) * (rexp τ - 1 - τ) = σ ^ 2 * (rexp τ - 1 - τ) := by
          by_cases h : rexp τ - 1 - τ = 0
          · rw [h]
            simp [mul_zero]
          · suffices (∫ (a : Ω), X i a ^ 2 ∂μ) = σ ^ 2 by simp [h]; exact this
            have this := (hσ i)
            simp [this]
        rw [hmu2]
        suffices 1 + σ ^ 2 * (rexp τ - 1 - τ) ≤ rexp (σ ^ 2 * (rexp τ - 1 - τ)) by linarith
        have this := add_one_le_exp (σ ^ 2 * (rexp τ - 1 - τ))
        simp only [add_comm] at this
        exact this
      have h_nonneg : ∀ i, 0 ≤ ∫ ω, rexp (τ * X i ω) ∂μ := by
          intro i
          exact integral_nonneg (fun ω => (exp_pos _).le)
      have h_n : n * σ ^ 2 * (rexp τ - 1 - τ) = ∑ i : Fin n, σ ^ 2 * (rexp τ - 1 - τ) := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc];
      simp only [h_n]
      rw [exp_sum]
      let s : Finset (Fin n) := Finset.univ
      apply Finset.prod_le_prod (s := s)
      · intro i _
        exact integral_nonneg (fun ω => (exp_pos _).le)
      · intro i _
        exact this i
    have h_single_plus : rexp (-(τ * ε)) * ∏ i, ∫ (ω : Ω), rexp (τ * X i ω) ∂μ ≤ rexp (-(τ * ε) + n * σ ^ 2 * (rexp τ - 1 - τ)) := by
      have this : (rexp (-(τ * ε))) ≥ 0 := by positivity
      rw [exp_add]
      nlinarith [this, h_single]
    exact h_single_plus


theorem bennett_inequality
    {n : ℕ}
    (hn : n > 0)
    {X : Fin n → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ)
    (hX_bdd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hμX : ∀ i, μ[X i] = 0)
    (σ : ℝ)
    (hσ_pos : σ > 0)
    (hσ : ∀ i, σ ^ 2 = μ[X i^2])
    (ε : ℝ)
    (hε : ε > 0) :
    (μ {ω | ∑ i, X i ω ≥ ε}).toReal ≤ exp (- (n * σ ^ 2 * bennett_h (ε / (n * σ ^ 2)))) := by
  let S := fun ω => ∑ i, X i ω
  have ht_sq : 0 ≤ σ^2 := by positivity
  have bennett_bound := bennett_bound (μ := μ) (n:=n) (X:=X) (hXm:=hXm) (hXi:=hXi) (hX_bdd:=hX_bdd) (hμX:=hμX) (σ:=σ) (hσ:=hσ) (ε:=ε)
  let τ_ := log (1 + ε / (n * σ ^ 2))
  have τ_nonneg : τ_ ≥ 0 := by
    have τ_pos : τ_ > 0 := by
      have : 1 + ε / (n * σ ^ 2) > 1 := by
        suffices ε / (n * σ ^ 2) > 0 by
          linarith
        exact div_pos hε (by positivity)
      exact log_pos this
    positivity
  have bennett_bound_τ_ := bennett_bound τ_ τ_nonneg
  have bound : (μ {ω | ∑ i, X i ω ≥ ε}).toReal ≤ rexp (-(log (1 + ε / (n * σ ^ 2)) * ε) + ↑n * σ ^ 2 * (1 + ε / (n * σ ^ 2) - 1 - log (1 + ε / (n * σ ^ 2)))) := by
    unfold τ_ at bennett_bound_τ_
    rw [exp_log] at bennett_bound_τ_
    exact bennett_bound_τ_
    positivity
  have : ↑n * σ ^ 2 * (1 + ε / (↑n * σ ^ 2) - 1 - log (1 + ε / (↑n * σ ^ 2))) = ε - ↑n * σ ^ 2 * log (1 + ε / (↑n * σ ^ 2)) := by
    field_simp
  rw [this] at bound
  unfold bennett_h
  have : rexp (-(↑n * σ ^ 2 * ((1 + ε / (↑n * σ ^ 2)) * log (1 + ε / (↑n * σ ^ 2)) - ε / (↑n * σ ^ 2)))) = rexp (-(↑n * σ ^ 2 * log (1 + ε / (↑n * σ ^ 2)) + ε * log (1 + ε / (↑n * σ ^ 2)) - ε)) := by
    have pos : ↑n * σ ^ 2 > 0 := by positivity
    field_simp [pos]
    ring_nf
  rw [this]
  let z := log (1 + ε / (n * σ ^ 2))
  have hz : z = log (1 + ε / (n * σ ^ 2)) := by rfl
  rw [<-hz] at bound
  rw [<-hz]
  suffices rexp (-(z * ε) + (ε - ↑n * σ ^ 2 * z)) = rexp (-(↑n * σ ^ 2 * z + ε * z - ε)) by linarith
  apply exp_eq_exp.mpr
  field_simp
  linarith
