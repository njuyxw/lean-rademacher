import FoML.ForMathlib.Probability.Moments
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Probability.Variance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import FoML.ForMathlib.Probability.Moments
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring.RingNF

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
import FoML.Bennett

open scoped Topology
open MeasureTheory ProbabilityTheory BigOperators ENNReal Real Set Filter Asymptotics

universe u
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {n : ℕ} {X : Fin n → Ω → ℝ}

noncomputable def bernstein_h (u : ℝ) : ℝ := u ^ 2 / ((1 + u / 3) * 2)
noncomputable def f (u: ℝ): ℝ := bennett_h u - bernstein_h u

lemma bernstein_h_bound (v : ℝ) (hv_pos : 0 ≤ v):
    bernstein_h v ≤ bennett_h v := by
  simp [bernstein_h]
  simp [bennett_h]
  apply le_of_sub_nonpos
  have hdp: (2 * (1 + v / 3)) > 0 := by linarith
  set f : ℝ → ℝ := fun u => u ^ 2 / ((1 + u / 3) * 2) - ((1 + u) * log (1 + u) - u)
  set f' : ℝ → ℝ := fun u => (18 * u + 3 * u ^ 2) / (2 * (u + 3) ^ 2) - log (1 + u)
  set f'' : ℝ → ℝ := fun u => 1 / (1 + u / 3)^3 - 1 / (1 + u)
  change f v ≤ 0
  have hf0 : f 0 = 0 := by simp [f]
  have hf'0 : f' 0 = 0 := by simp [f']
  rw [← hf0]
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (by
    apply ContinuousOn.sub
    · apply ContinuousOn.div
      · exact continuousOn_id.pow 2
      · apply ContinuousOn.mul
        · apply ContinuousOn.add
          · exact continuousOn_const
          · apply ContinuousOn.mul
            · exact continuousOn_id
            · exact continuousOn_const
        · exact continuousOn_const
      · intro x hx
        have h : 0 ≤ x := by exact hx
        field_simp
    · apply ContinuousOn.sub
      · apply ContinuousOn.mul
        · apply ContinuousOn.add
          · exact continuousOn_const
          · exact continuousOn_id
        · apply ContinuousOn.log
          · apply ContinuousOn.add
            · exact continuousOn_const
            · exact continuousOn_id
          · intro x hx
            have h : 0 ≤ x := by exact hx
            have h1 : 0 < 1 + x := by linarith
            apply ne_of_gt
            field_simp
            exact h1
      · exact continuousOn_id
  )
    (fun t ht  =>
    (HasDerivAt.sub
    (HasDerivAt.div ((hasDerivAt_id t).pow 2) ((HasDerivAt.const_add 1 ((hasDerivAt_id t).div_const 3)).mul_const 2) (by
    field_simp
    apply mul_ne_zero
    case ha =>
      have h1 : t > 0 := by
        rw [interior_Ici] at ht
        exact ht
      linarith
    case hb =>
      norm_num
    ))
    (((HasDerivAt.const_add 1 (hasDerivAt_id t)).mul (HasDerivAt.log (HasDerivAt.const_add 1 (hasDerivAt_id t)) (by
      apply ne_of_gt
      apply add_pos_of_nonneg_of_pos
      field_simp
      have h1 : 0 < t := by
        rw [interior_Ici] at ht
        exact ht
      field_simp
      exact h1
    ) )).sub (hasDerivAt_id t))
    ).hasDerivWithinAt)
    (fun k hk => ?_) left_mem_Ici hv_pos hv_pos
  field_simp
  have hk' : 0 < k := by
    rw [interior_Ici] at hk
    rw [mem_Ioi] at hk
    exact hk
  have hk1' : 1 + k ≠ 0 := by
    apply ne_of_gt
    apply add_pos_of_nonneg_of_pos
    linarith
    exact hk'
  rw [div_self hk1']
  field_simp
  apply le_of_sub_nonpos
  have eqv: (2 * k * ((3 + k) * 2) - k ^ 2 * 2) * 3 ^ 2 = (108 * k + 18 * k ^ 2) := by linarith
  rw [eqv]
  have eqv: (3 * ((3 + k) * 2) ^ 2) = 12 * (k+3) ^ 2:= by linarith
  rw [eqv]
  have eqv: (108 * k + 18 * k ^ 2) / (12 * (k + 3) ^ 2) = (18 * k + 3 * k ^ 2) / (2 * (k + 3) ^ 2):= by field_simp; linarith;
  rw [eqv]
  show f' k ≤ 0
  rw [← hf'0]
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (by
    apply ContinuousOn.sub
    · apply ContinuousOn.div
      · apply ContinuousOn.add
        · exact continuousOn_const.mul continuousOn_id
        · exact continuousOn_const.mul (continuousOn_id.pow 2)
      · apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.pow
        apply ContinuousOn.add continuousOn_id continuousOn_const
      · intro x hx
        have h : 0 ≤ x := hx
        have h' : 0 < 2 * (x + 3) ^ 2 := by positivity
        exact ne_of_gt h'
    · apply ContinuousOn.log
      · apply ContinuousOn.add continuousOn_const continuousOn_id
      · intro x hx
        have h : 0 ≤ x := hx
        have h' : 0 < 1 + x := by linarith
        exact ne_of_gt h'
  )
    (fun t ht =>
      (HasDerivAt.sub
        (HasDerivAt.div
          (
            HasDerivAt.add
            (HasDerivAt.const_mul 18 (hasDerivAt_id t))
            (HasDerivAt.const_mul 3 ((hasDerivAt_id t).pow 2))
          )
          (HasDerivAt.const_mul 2 (((hasDerivAt_id t).add_const 3).pow 2))
          (by
            have ht' : 0 < t := by
              rw [interior_Ici] at ht
              rw [mem_Ioi] at ht
              exact ht
            have ht1' : 0 < 3 + t:= by
              apply add_pos_of_nonneg_of_pos
              norm_num
              exact ht'
            have ht2' : 0 < (3 + t) ^ 2 := by
              apply sq_pos_of_pos
              exact ht1'
            have ht3' : 0 < 2 * (3 + t) ^ 2 := by linarith
            have ht4' : 2 * (3 + t) ^ 2 ≠ 0 := by
              apply ne_of_gt
              exact ht3'
            field_simp
        ))
        (
          HasDerivAt.log (HasDerivAt.const_add 1 (hasDerivAt_id t))
          (by
            have ht' : 0 < t := by
              rw [interior_Ici] at ht
              rw [mem_Ioi] at ht
              exact ht
            have ht1' : 0 < 1 + t := by
              apply add_pos_of_nonneg_of_pos
              norm_num
              exact ht'
            have ht2' : ¬ 1 + t = 0 := by
              apply ne_of_gt
              exact ht1'
            field_simp
            exact ht2'
          )
        )
      ).hasDerivWithinAt)
    (fun k hk => ?_) left_mem_Ici (interior_subset hk) (interior_subset hk)
  field_simp
  have eqv: (2 * (k + 3) ^ 2) ^ 2 = 4 * (k + 3) ^ 4 := by ring_nf
  rw [eqv]
  have eqv: ((18 + 3 * (2 * k)) * (2 * (k + 3) ^ 2) - (18 * k + 3 * k ^ 2) * (2 * (2 * (k + 3)))) = 108 * (k + 3) := by ring_nf;
  rw [eqv]
  have hk' : 0 < k := by
    rw [interior_Ici] at hk
    rw [mem_Ioi] at hk
    exact hk
  have hk1' : 1 + k ≠ 0 := by
    apply ne_of_gt
    apply add_pos_of_nonneg_of_pos
    linarith
    exact hk'
  have hk3' : k + 3 ≠ 0 := by
    apply ne_of_gt
    apply add_pos_of_nonneg_of_pos
    linarith
    norm_num
  apply le_of_sub_nonpos
  have eqv: 108 * (k + 3) / (4 * (k + 3) ^ 4) - 1 / (1 + k) = (108 * (k + 3) * (k + 1) - (4 * (k + 3) ^ 4)) / (4 * (k + 3) ^ 4 * (1 + k)) := by
    field_simp
    linarith
  rw [eqv]
  have eqv: (108 * (k + 3) * (k + 1) - (4 * (k + 3) ^ 4)) = -4 * k^4 - 48 * k^3 - 108 * k^2 := by ring_nf
  rw [eqv]
  have hup: -4 * k^4 - 48 * k^3 - 108 * k^2 ≤ 0 := by
    have : -4 * k^4 - 48 * k^3 - 108 * k^2 = -4 * k^2 * (k+3) * (k+9) := by ring_nf
    rw [this]
    have h1 : -4 * k^2 ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · norm_num
      · exact pow_two_nonneg k
    have h2: -4 * k^2 * (k + 3) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · linarith
      · linarith
    have h3: -4 * k^2 * (k + 3) * (k + 9)≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · linarith
      · linarith
    exact h3
  have hdown: 0 ≤ (4 * (k + 3) ^ 4 * (1 + k)) := by
    have h1 : 0 ≤ (k + 3) ^ 2 := by
      apply pow_two_nonneg
    have h2 : 0 ≤ ((k + 3) ^ 2) ^ 2 := by
      apply pow_two_nonneg
    have h3 : 0 ≤ (k + 3) ^ 4 := by
      have : ((k + 3) ^ 4) = (((k + 3) ^ 2) ^ 2) := by ring_nf
      rw [this]
      exact h2
    have h4 : 0 ≤ 1 + k := by apply add_nonneg; linarith; linarith
    have h5 : 0 ≤ 4 * (k + 3) ^ 4 := by
      apply mul_nonneg
      norm_num
      exact h3
    have h7 : 0 ≤ 4 * (k + 3) ^ 4 * (1 + k) := by
      apply mul_nonneg;
      exact h5
      exact h4
    exact h7
  apply div_nonpos_of_nonpos_of_nonneg
  exact hup
  exact hdown

theorem bernstein_inequality
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
    (μ {ω | ∑ i, X i ω ≥ ε}).toReal ≤ exp (- ε ^ 2 / (2 * n * σ ^ 2 + 2 / 3 * ε)) := by

  have bernstein_relax: exp (- (n * σ ^ 2 * bennett_h (ε / (n * σ ^ 2)))) ≤ exp (- ε ^ 2 / (2 * n * σ ^ 2 + 2 / 3 * ε)) := by
    apply exp_le_exp.mpr
    have h0: n * σ ^ 2 ≥ 0 := by
      have ha: (n : ℝ) ≥ 0 := by positivity
      have hb: σ ^ 2 ≥ 0 := by positivity
      exact mul_nonneg ha hb
    have h1: ε / (↑n * σ ^ 2) ≥ 0 := by
      apply div_nonneg
      · have : ε ≥ 0 := by linarith
        exact this
      · exact h0
    have h2: bennett_h (ε / (↑n * σ ^ 2)) ≥ bernstein_h (ε / (↑n * σ ^ 2)) := by
      apply bernstein_h_bound
      exact h1
    have h3: n * σ ^ 2 * bennett_h (ε / (↑n * σ ^ 2)) ≥ n * σ ^ 2 * bernstein_h (ε / (↑n * σ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left h2
      exact h0
    have h4: - (↑n * σ ^ 2 * bennett_h (ε / (↑n * σ ^ 2))) ≤ - (↑n * σ ^ 2 * bernstein_h (ε / (↑n * σ ^ 2))) := by
      apply neg_le_neg
      exact h3
    unfold bernstein_h at h4
    have h5: -(↑n * σ ^ 2 * ((ε / (↑n * σ ^ 2)) ^ 2 / ((1 + ε / (↑n * σ ^ 2) / 3) * 2))) = - ε^2 / (2 * ↑n * σ ^ 2 + 2 / 3 * ε) := by
      field_simp
      ring_nf
    rw [h5] at h4
    exact h4

  have bennett_inequality := bennett_inequality (μ := μ) (n:=n) (X:=X) (hXm:=hXm) (hXi:=hXi) (hX_bdd:=hX_bdd) (hμX:=hμX) (σ:=σ) (hσ:=hσ) (ε:=ε) (hσ_pos:=hσ_pos) (hε:=hε) (hn:=hn)

  linarith [bennett_inequality, bernstein_relax]
