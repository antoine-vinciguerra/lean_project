import Mathlib.Tactic.Basic

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Order.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.Filter.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Analysis.Complex.Basic

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Commute.Defs
import LaplaceTransform.LaplaceTransformDef
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.Analysis.Complex.Exponential

import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv


/-!


# The Real Version of the Laplace transform

-/

@[expose] public section


noncomputable section


open MeasureTheory Filter
open MeasureTheory Set
open scoped Topology
open Complex

section Defs
-- Define the function L
def realLine : Set ℂ := {z : ℂ | z.im = 0}
def realLine_to_real (z : realLine) : ℝ :=
  z.val.re
--functions to go from R to our realLine
def real_to_realLine (x : ℝ) : realLine :=
  ⟨(x : ℂ), show ((x : ℂ).im = 0) from by simp⟩

def L (x: realLine)  (z:ℂ ) :  ℂ:=
  x * z

-- Define the set [0, ∞)

def nonNegativeRealLine : Set realLine :=
  {z : realLine | z.val.re ≥ 0}
def non_negative_reals : Set ℝ := Ici 0


-- Define the measure on [0, ∞) as the Lebesgue measure restricted to that set
def μ_real : Measure ℝ := volume.restrict non_negative_reals
def μ_r : Measure realLine :=
  Measure.map real_to_realLine μ_real



-- Now define the same for the right hand halfplane of the complex

def RealFullLaplaceKernel (f :ℝ → ℂ) (p : ℂ) : realLine→ ℂ :=
  let g (x : realLine): ℂ:= f (realLine_to_real x)
  fun x ↦(fullLaplaceKernel realLine L g p) x


def RealLaplaceTransform (f :ℝ  → ℂ) : ℂ → ℂ  :=
  let g (x : realLine): ℂ:= f (realLine_to_real x)
  GeneralizedLaplaceTransform realLine L g μ_r

 --definiton of the laplace transfom
noncomputable def laplaceTransform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t in Ioi 0, f t * cexp (-s * t)

  --definition of the laplace transform in the pre-limit
noncomputable def finiteLaplaceTransform (f : ℝ → ℂ) (s : ℂ) (T : ℝ) : ℂ :=
  ∫ t in Ioc 0 T, f t * cexp (-s * t)


-- we show that the finite laplace transform converges to the Laplace transform as T converges
-- to infinity
theorem finite_laplace_tendsto_laplace (f : ℝ → ℂ) (s : ℂ)
    (h_int : IntegrableOn (fun t ↦ f t * cexp (-s * t)) (Ioi 0)) :
    Tendsto (fun T ↦ finiteLaplaceTransform f s T) atTop (𝓝 (laplaceTransform f s)) := by
    simp only [laplaceTransform, finiteLaplaceTransform]
    -- we re-write the finite integral over (0, T] as an integral over (0, ∞) using an indiccator
    -- function so the we can apply the dominated convergence theorem
    have h_eq : (fun T ↦ ∫ (t : ℝ) in Ioc 0 T, f t * cexp (-s * ↑t)) =
              (fun T ↦ ∫ (t : ℝ) in Ioi 0, (Iic T).indicator (fun t ↦ f t * cexp (-s * ↑t)) t) := by
              ext T
              -- Use the identity (0, T] = (0, ∞) ∩ (-∞, T]
              have : Ioc (0:ℝ) T = Ioi 0 ∩ Iic T := Ioi_inter_Iic.symm
              rw [this]
              exact (setIntegral_indicator measurableSet_Iic).symm
    rw [h_eq]
    -- we apply the dominated convergence theorem
    apply tendsto_integral_filter_of_dominated_convergence
    -- we show the sequence is a.e. strongly measurable
    filter_upwards
    intro T
    exact h_int.aestronglyMeasurable.indicator measurableSet_Iic
    -- we show the dominating function is the integrand
    apply Filter.Eventually.of_forall
    intro n
    apply Filter.Eventually.of_forall
    intro a
    rw [Set.indicator_apply]
    split_ifs
    ·
      exact le_rfl
    ·
      simp [norm_nonneg]
    -- we show integrability of the integrand/the dominating function
    simp_all only [neg_mul, Complex.norm_mul]
    have h_norm : ∀ a > 0, ‖f a‖ * ‖cexp (-(s * ↑a))‖ = ‖f a‖ * exp (-(s.re * a)) := by
      intro a ha
      simp_rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re,
         Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      push_cast
      rfl
    have h_norm_int : Integrable (fun t => ‖f t * cexp (-(s * ↑t))‖) (volume.restrict (Ioi 0)) := Integrable.norm h_int
    simp_rw [norm_mul] at h_norm_int
    exact h_norm_int
    -- we how the sequence of functions converges pointwise a.e.
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi)] with a ha
    have h_eventually : ∀ᶠ n in atTop, (Iic n).indicator (fun t ↦ f t * cexp (-s * ↑t)) a = f a * cexp (-s * ↑a) := by
      filter_upwards [eventually_ge_atTop a] with n hn
      rw [Set.indicator_of_mem]
      exact hn
    apply Filter.EventuallyEq.tendsto h_eventually



-- The following theorems are on the finite Laplace transform, also know at the truncated Laplace
-- transform. Subsequently we will take the limit and prove the corresponding theorems for the
-- Laplace transform



--we show that the laplace transform in the pre-limit is linear
theorem finiteLaplaceTransform_linear
    (f g : ℝ → ℂ) (s a b : ℂ) (T : ℝ)
    (hf : IntegrableOn (fun t ↦ f t * cexp (-s * t)) (Ioc 0 T))
    (hg : IntegrableOn (fun t ↦ g t * cexp (-s * t)) (Ioc 0 T)) :
    finiteLaplaceTransform (fun t ↦ a * f t + b * g t) s T =
    a * finiteLaplaceTransform f s T + b * finiteLaplaceTransform g s T := by
  unfold finiteLaplaceTransform
  simp only [add_mul, mul_assoc]
  rw [integral_add (hf.const_mul a) (hg.const_mul b)]
  rw [integral_const_mul, integral_const_mul]

-- we show that the truncated laplace transform evaluated at 1 is equal to e^{-s T}/(-s)
-- - e^{-s 0}/(-s)
theorem finite_laplace_of_one_eq_eval (s : ℂ) (T : ℝ) (hs : s ≠ 0)(hT : 0 ≤ T) :
    finiteLaplaceTransform (fun _ ↦ 1) s T = (cexp (-s * T) / -s) - (cexp (-s * 0) / -s) := by
    unfold finiteLaplaceTransform
    simp only [one_mul]
    rw [← intervalIntegral.integral_of_le hT]
    -- we define the antiderivative of the integrand
    let F := fun (t : ℝ) ↦ cexp (-s * t) / -s
    -- we show that F is in fact the antiderivative of the integrand
    have h_deriv : ∀ t ∈ Set.uIcc 0 T, HasDerivAt F (cexp (-s * t)) t := by
      intro t _
      dsimp [F]
      have h_inner : HasDerivAt (fun (x : ℝ) ↦ -s * x) (-s) t := by
        simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id t)).const_mul (-s)
      convert HasDerivAt.div_const (h_inner.cexp) (-s) using 1
      have h_exp := h_inner.cexp
      field_simp [hs]
    -- we apply the fundamental theorem of calculus
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    exact h_deriv
    -- we show integrability of the integrand by stating its continuity
    apply Continuous.intervalIntegrable
    continuity


-- we show that the truncated laplace transform evaluated at t is equal to 1/(s^2)(1 - e^{-s T}/(-s)
-- - e^{-s T}/(-s)) - (T e^{-s*T}/s)
theorem finite_laplace_of_t_eq_eval (s : ℂ) (T : ℝ) (hs : s ≠ 0) (hT : 0 ≤ T) :
    finiteLaplaceTransform (fun t ↦ (t : ℂ)) s T =
    (1 / s^2) * (1 - cexp (-s * T)) - ((T : ℂ) * cexp (-s * T) / s) := by
    unfold finiteLaplaceTransform
    simp only
    rw [← intervalIntegral.integral_of_le hT]
    -- we define the functions in the integration by parts formula  ∫uv' = uv - ∫u'v
    let u := fun (t : ℝ) ↦ (t : ℂ)
    let v := fun (t : ℝ) ↦  cexp (-s * t)/ -s
    -- we show that u is differentiable
    have hu : ∀ t ∈ Set.uIcc 0 T, HasDerivAt u (1) t := by
      intro t _
      dsimp [u]
      exact (hasDerivAt_id t).ofReal_comp
    -- we show that v is differentiable
    have hv : ∀ t ∈ Set.uIcc 0 T, HasDerivAt v (cexp (-s * t)) t := by
      intro t _
      dsimp [v]
      have h_inner : HasDerivAt (fun (x : ℝ) ↦ -s * x) (-s) t := by
        simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id t)).const_mul (-s)
      convert HasDerivAt.div_const (h_inner.cexp) (-s) using 1
      have h_exp := h_inner.cexp
      field_simp [hs]
    -- we apply integration by parts
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv]
    rotate_left
    -- we show integrability of the integrands by stating their continuity
    case hu' =>
      apply Continuous.intervalIntegrable
      continuity
    case hv' =>
      apply Continuous.intervalIntegrable
      continuity
    simp only [one_mul]
    dsimp [u, v]
    simp only [mul_zero, zero_mul, sub_zero]
    -- we define the antiderivaitve of the integrand that is left after applying integration by parts
    let F := fun (t : ℝ) ↦ cexp (-s * t)/ (-s)^2
    -- we show that the antiderivative is differnetiable
    have h_deriv : ∀ t ∈ Set.uIcc 0 T, HasDerivAt F (cexp (-s * t)/ -s) t := by
      intro t _
      dsimp[F]
      have h_inner : HasDerivAt (fun (x : ℝ) ↦ -s * x) (-s) t := by
        simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id t)).const_mul (-s)
      convert h_inner.cexp.div_const ((-s) ^ 2) using 1
      field_simp
    -- we apply the fundamental theorem of calculus
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv]
    rotate_left
    -- we show integrability of the integrand by stating it's continuity
    apply Continuous.intervalIntegrable
    continuity
    dsimp [F]
    field_simp [hs]
    simp
    ring

-- we show that the truncated laplace transform evaluated at t^k/(k!) is equal to
theorem finiteLaplaceTransform_pow_div_factorial (k : ℕ) (s : ℂ) (T : ℝ) (hs : s ≠ 0)(hT : 0 ≤ T) :
    finiteLaplaceTransform (fun t => (t : ℂ) ^ k / (k.factorial : ℂ)) s T =
    (1 / s^(k + 1)) * (1 - cexp (-s * (T : ℂ)) * ∑ j ∈ Finset.range (k + 1), (s * (T : ℂ))^j / (j.factorial : ℂ)) := by
    -- we prove this result by induction
    induction k
    -- we do the base case
    case zero =>
      unfold finiteLaplaceTransform
      simp only [one_mul]
      rw [← intervalIntegral.integral_of_le hT]
      --we define the antiderivative of the integrand
      let F := fun (t : ℝ) ↦ cexp (-s * t) / -s
      -- we show the derivative of F with respect to t is e^{-s t}
      have h_deriv : ∀ t ∈ Set.uIcc 0 T, HasDerivAt F (cexp (-s * t)) t := by
        intro t _
        dsimp [F]
        --we show the derivative of -s x with respect to x is -s
        have h_inner : HasDerivAt (fun (x : ℝ) ↦ -s * x) (-s) t := by
          simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id t)).const_mul (-s)
        convert HasDerivAt.div_const (h_inner.cexp) (-s) using 1
        have h_exp := h_inner.cexp
        field_simp [hs]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
      -- we apply the fundamental theorem of calculus
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv]
      dsimp [F]
      simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
               Finset.range_one, Finset.sum_singleton, pow_one]
      field_simp [hs]
      ring
      rw [Complex.exp_zero] at *
      ring
      -- we show integrability of the integrand by stating continuity
      apply Continuous.intervalIntegrable
      continuity
    case succ k ih =>
      unfold finiteLaplaceTransform
      simp only
      rw [← intervalIntegral.integral_of_le hT]
      -- we define the functions in the integration by parts formula  ∫uv' = uv - ∫u'v
      let u := fun (t : ℝ) ↦ (t: ℂ) ^ (k + 1) / (k + 1).factorial
      let v := fun (t : ℝ) ↦ cexp (-s * t)/ -s
      -- we show that u has as derivative t ^ k / k.factorial
      have hu : ∀ t ∈ Set.uIcc 0 T, HasDerivAt u (t ^ k / k.factorial) t := by
        intro t _
        dsimp[u]
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
        convert HasDerivAt.ofReal_comp ((hasDerivAt_pow (k + 1) t).div_const ((k + 1 : ℝ) * k.factorial)) using 1
        ext x
        simp
        rw [Nat.add_sub_cancel]
        field_simp
        push_cast
        field_simp
      -- we show that v has as derivative cexp (-s * t)
      have hv : ∀ t ∈ Set.uIcc 0 T, HasDerivAt v (cexp (-s * t)) t := by
        intro t _
        dsimp [v]
        have h_inner : HasDerivAt (fun (x : ℝ) ↦ -s * x) (-s) t := by
          simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id t)).const_mul (-s)
        convert HasDerivAt.div_const (h_inner.cexp) (-s) using 1
        have h_exp := h_inner.cexp
        field_simp [hs]
      -- we integrate by parts
      rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv]
      -- we show integrability of the integrands by stating their continuity
      rotate_left
      case hu' =>
        apply Continuous.intervalIntegrable
        continuity
      case hv' =>
        apply Continuous.intervalIntegrable
        continuity
      dsimp [u, v]
      simp only [zero_pow (Nat.succ_ne_zero k), zero_div, mul_zero, sub_zero, mul_div_assoc, zero_mul]
      simp_rw [div_eq_mul_inv, mul_assoc]
      -- we now setup applying the inductive hypothesis
      unfold finiteLaplaceTransform at ih
      rw [← intervalIntegral.integral_of_le hT] at ih
      simp_rw [← mul_assoc]
      rw [intervalIntegral.integral_mul_const]
      simp only [div_eq_mul_inv] at ih
      -- we apply the inductive hypothesis
      rw [ih]
      -- we simplify the expression
      field_simp [hs]
      rw [Finset.sum_range_succ]
      rw [← Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [← Finset.sum_range_succ _ k]
      rw [Finset.sum_range_succ _ (k + 1)]
      simp only [pow_succ, div_eq_mul_inv]
      ring

-- we show that the Laplace transform of e^{at} is equal to (1 - e^{-(s - a)T})/(s - a)
theorem finite_laplace_of_exp_eq (a s : ℂ) (T : ℝ) (h : s ≠ a) (hT : 0 ≤ T) :
  finiteLaplaceTransform (fun t ↦ cexp (a * t)) s T = (1 - cexp (-(s - a) * T)) / (s - a) := by
  unfold finiteLaplaceTransform
  simp only [one_mul]
  rw [← intervalIntegral.integral_of_le hT]
  simp_rw [← Complex.exp_add, ← add_mul]
  simp_rw [← sub_eq_add_neg]
  -- we define the antiderivative of the integrand
  let F := fun (t : ℝ) ↦ cexp ((a-s) * t) / (a-s)
  -- we show the antiderivatiev of F is e^{(a - s)t}
  have h_deriv : ∀ t ∈ Set.uIcc 0 T, HasDerivAt F (cexp ((a-s) * t)) t := by
    intro t _
    dsimp [F]
    -- we show that the derivatiev of (a - s)x is a - s
    have h_inner : HasDerivAt (fun (x : ℝ) ↦ (a-s) * x) (a-s) t := by
      simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id t)).const_mul (a-s)
    convert HasDerivAt.div_const (h_inner.cexp) (a-s) using 1
    have h_exp := h_inner.cexp
    field_simp [h]
    rw [div_self (sub_ne_zero.mpr h.symm)]
  -- we apply the undamental theorem of calculus
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ h_deriv t ht)]
  -- we make sime final simplfications
  dsimp [F]
  rw [← sub_div]
  rw [neg_sub s a]
  rw [mul_zero, Complex.exp_zero]
  rw [←neg_sub a s]
  rw [div_neg]
  ring
  -- we show that the integrand is integrable by stating its continuity
  apply Continuous.intervalIntegrable
  continuity

-- we show that the truncated laplace transform L of the derivative of a function f is s L[s]
-- - f(0) + e^{- s T}f(T)
theorem finite_laplace_deriv_eq (f df : ℝ → ℂ) (s : ℂ) (T : ℝ)
    (hT : 0 ≤ T)
    (hf : ∀ t ∈ Set.Icc 0 T, HasDerivAt f (df t) t)
    (hf_int : IntervalIntegrable df volume 0 T)
    (h_cont : ContinuousOn df (Set.Icc 0 T))
    (hf_int : IntervalIntegrable df volume 0 T) :
  finiteLaplaceTransform df s T = s * finiteLaplaceTransform f s T - f 0 + cexp (-s * T) * f T := by
  unfold finiteLaplaceTransform
  rw [← intervalIntegral.integral_of_le hT]
  -- we define the functions in the integral which correspond to integration by parts
  let u := fun (t : ℝ) ↦  cexp (-s * t)
  let v := fun (t : ℝ) ↦ f t
  -- we show that the deriavei of u is -s * e^{-s * t}
  have hu : ∀ t ∈ Set.uIcc 0 T, HasDerivAt u (-s * cexp (-s * t)) t := by
    intro t _
    dsimp [u]
    have h_inner : HasDerivAt (fun (x : ℝ) ↦ -s * x) (-s) t := by
        simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id t)).const_mul (-s)
    convert h_inner.cexp using 1
    ring
  -- we show that the derivative of v is f'
  have hv : ∀ t ∈ Set.uIcc 0 T, HasDerivAt v (df t) t := by
    rw [Set.uIcc_of_le hT]
    exact hf
  rw [intervalIntegral.integral_congr (fun t _ ↦ mul_comm (df t) (u t))]
  -- we apply the integration by parts
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv]
  simp only [u, v]
  ring_nf
  simp only [intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_of_le hT]
  simp
  ring
  rotate_left
  -- we show integrability of the integrands by stating their continuity
  case hu' =>
    apply Continuous.intervalIntegrable
    continuity
  case hv' =>
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact h_cont
  -- we simplify the expression to complete the proof
  rw [add_comm]
  congr 1
  simp_rw [mul_assoc, mul_comm (cexp _) (f _), ← mul_assoc]
  simp_all only [mem_Icc, and_imp, uIcc_of_le, neg_mul, implies_true, u, v]
  simp_rw [mul_assoc, MeasureTheory.integral_const_mul]


-- we show that the nth derivaitve of the truncated laplace transform of s is ...
theorem finite_laplace_iteratedDeriv_eq (f : ℝ → ℂ) (s : ℂ) (T : ℝ) (n : ℕ)
    (hT : 0 ≤ T)
    (hf_cont_diff : ContDiff ℝ (n) f)
    (hf_int : IntervalIntegrable (iteratedDeriv n f) volume 0 T) :
  finiteLaplaceTransform (iteratedDeriv n f) s T =
    s^n * finiteLaplaceTransform f s T
    - (∑ k ∈ Finset.range n, s^(n - 1 - k) * iteratedDeriv k f 0)
    + cexp (-s * T) * (∑ k ∈ Finset.range n, s^(n - 1 - k) * iteratedDeriv k f T) := by
  -- we proceed by indufction
  induction n
  case zero =>
    -- the base case at 0 is simple
    unfold finiteLaplaceTransform
    simp [iteratedDeriv]
  case succ n ih =>
    -- we show at the truncated laplace transform of the n+1 derivative  is s times the truncated laplace transform of  the nth derivative
    have h_deriv : finiteLaplaceTransform (iteratedDeriv (n + 1) f) s T =
        s * finiteLaplaceTransform (iteratedDeriv n f) s T
        - iteratedDeriv n f 0
        + cexp (-s * T) * iteratedDeriv n f T := by
        apply finite_laplace_deriv_eq
        exact hT
        rw [iteratedDeriv_succ]
        intro t ht
        apply DifferentiableAt.hasDerivAt
        -- we show that the derivative that the nth derivative is differentiable at t
        have h_diff : Differentiable ℝ (iteratedDeriv n f) := ContDiff.differentiable_iteratedDeriv n hf_cont_diff (by norm_cast; omega)
        exact h_diff t
        -- we conclude by showing integrability and continuity of the n+1 derivative of
        apply Continuous.intervalIntegrable
        exact hf_cont_diff.continuous_iteratedDeriv (n + 1) le_rfl
        exact (hf_cont_diff.continuous_iteratedDeriv (n + 1) le_rfl).continuousOn
        assumption
    -- we show that f is continuisly differentiable n time
    have h_cont_n : ContDiff ℝ (↑n) f := hf_cont_diff.of_le (by norm_cast; omega)
    -- we show that the nth derivative of f is integrable over 0, T
    have h_int_n : IntervalIntegrable (iteratedDeriv n f) volume 0 T := by
      apply Continuous.intervalIntegrable
      exact h_cont_n.continuous_iteratedDeriv n le_rfl
    -- we apply the inductive hypothesis
    have ih_spec := ih h_cont_n h_int_n
    rw [h_deriv, ih_spec]
    have h_exp : n + 1 - 1 = n := by omega
    simp_rw [h_exp, Finset.sum_range_succ]
    have h_nn : n - n = 0 := Nat.sub_self n
    simp_rw [h_nn, pow_zero, one_mul]
    -- we factor by s
    have h_sum_0 : (∑ k ∈ Finset.range n, s ^ (n - k) * iteratedDeriv k f 0) = s * ∑ k ∈ Finset.range n, s ^ (n - 1 - k) * iteratedDeriv k f 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have : n - k = n - 1 - k + 1 := by omega
      rw [this, pow_add, pow_one]
      ring
    -- we factor  s
    have h_sum_T : (∑ k ∈ Finset.range n, s ^ (n - k) * iteratedDeriv k f T) = s * ∑ k ∈ Finset.range n, s ^ (n - 1 - k) * iteratedDeriv k f T := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have : n - k = n - 1 - k + 1 := by omega
      rw [this, pow_add, pow_one]
      ring

    rw [h_sum_0, h_sum_T]
    ring

-- we now prove the the basic theorems of the Laplace transform by taking the limit

-- we show that the Laplace transform of 1 is 1/s
theorem laplace_of_one_eq_inv_s (s : ℂ) (hs : 0 < s.re) :
    laplaceTransform (fun _ ↦ 1) s = 1 / s := by
    have hs_ne_zero : s ≠ 0 := by
      intro h
      subst h
      simp at hs
    have h_int : IntegrableOn (fun (t : ℝ) ↦ 1 * cexp (-s * (t : ℂ))) (Ioi (0 : ℝ)) := by
      simp only [one_mul]
      have hs_neg : (-s).re < 0 := by
        rw [neg_re]
        exact neg_lt_zero.mpr hs
      exact integrableOn_exp_mul_complex_Ioi hs_neg 0
    have h_tendsto_laplace := finite_laplace_tendsto_laplace (fun _ ↦ 1) s h_int
    have h_tendsto_inv_s : Tendsto (fun T : ℝ ↦ (cexp (-s * ↑T) / -s) - (cexp (-s * 0) / -s)) atTop (𝓝 (1 / s)) := by
      have h_simp : (fun T : ℝ ↦ (cexp (-s * ↑T) / -s) - (cexp (-s * 0) / -s)) =
        fun T : ℝ ↦ (1 / -s) * cexp (-s * ↑T) + (1 / s) := by
        ext T
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
        ring
      rw [h_simp]
      have h_exp_zero : Tendsto (fun T : ℝ ↦ cexp (-s * ↑T)) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have h_norm : (fun T : ℝ ↦ ‖cexp (-s * ↑T)‖) = fun T : ℝ ↦ Real.exp (-s.re * T) := by
          ext T
          simp [Complex.mul_re]
          rw [Complex.norm_exp]
          congr 1
          simp
        rw [h_norm]
        have h_neg_re : -s.re < 0 := neg_lt_zero.mpr hs
        have h_atBot : Tendsto (fun T : ℝ ↦ -s.re * T) atTop atBot :=
        (Filter.tendsto_const_mul_atBot_of_neg h_neg_re).mpr Filter.tendsto_id
        exact Real.tendsto_exp_atBot.comp h_atBot
      have h_const : Tendsto (fun _ : ℝ ↦ 1 / s) atTop (𝓝 (1 / s)) := tendsto_const_nhds
      have h_final := Filter.Tendsto.add (Filter.Tendsto.const_mul (1 / -s) h_exp_zero) h_const
      simp only [mul_zero, zero_add] at h_final
      exact h_final

    have h_eventually_eq : (fun T : ℝ ↦ finiteLaplaceTransform (fun _ ↦ 1) s T) =ᶠ[atTop]
      (fun T : ℝ ↦ (cexp (-s * ↑T) / -s) - (cexp (-s * 0) / -s)) := by
      filter_upwards [Ici_mem_atTop (0 : ℝ)] with T hT
      exact finite_laplace_of_one_eq_eval s T hs_ne_zero hT
    exact tendsto_nhds_unique h_tendsto_laplace (Tendsto.congr' h_eventually_eq.symm h_tendsto_inv_s)

theorem laplace_of_t_eq_inv_s_sq (s : ℂ) (hs : 0 < s.re) :
    laplaceTransform (fun t ↦ t) s = 1 / s^2 := by
  have hs_ne_zero : s ≠ 0 := by
    intro h
    subst h
    simp at hs
  have h_int : IntegrableOn (fun (t : ℝ) ↦ (t : ℂ) * cexp (-s * (t : ℂ))) (Ioi (0 : ℝ)) := by
    have hs_neg : (-s).re < 0 := by
      rw [neg_re]
      exact neg_lt_zero.mpr hs
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    apply IntegrableOn.union
    apply ContinuousOn.integrableOn_compact
  have h_tendsto_laplace := finite_laplace_tendsto_laplace (fun t ↦ t) s h_int
  have h_exp_zero : Tendsto (fun T : ℝ ↦ cexp (-s * ↑T)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            mul_zero, sub_zero, neg_re]
    have h_neg_re : -s.re < 0 := neg_lt_zero.mpr hs
    exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg h_neg_re)
  have h_t_exp_zero : Tendsto (fun T : ℝ ↦ (T : ℂ) * cexp (-s * T)) atTop (𝓝 0) := by



  have h1 := Filter.Tendsto.const_mul (1 / s^2) (Filter.Tendsto.const_sub 1 h_exp_zero)
  have h2 := Filter.Tendsto.div_const h_t_exp_zero s
  simp only [sub_zero, mul_one] at h1
  exact Filter.Tendsto.sub h1 h2
  have h_eventually_eq : (fun T : ℝ ↦ finiteLaplaceTransform (fun t ↦ t) s T) =ᶠ[atTop]
      (fun T : ℝ ↦ (1 / s^2) * (1 - cexp (-s * T)) - (T * cexp (-s * T) / s)) := by
    filter_upwards [Ici_mem_atTop (0 : ℝ)] with T hT
    exact finite_laplace_of_t_eq_eval s T hs_ne_zero hT
  exact tendsto_nhds_unique h_tendsto_laplace (Tendsto.congr' h_eventually_eq.symm h_tendsto_inv_s_sq)
