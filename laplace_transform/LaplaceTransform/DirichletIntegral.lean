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
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Commute.Defs
import LaplaceTransform.LaplaceTransformDef
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.Filter.Prod

import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Filter.Basic

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
/-! # The Dirichlet Integral
-/


@[expose] public section


noncomputable section


open MeasureTheory Filter
open MeasureTheory Set
open MeasureTheory Complex Real Topology Filter
open scoped Topology
open Complex


noncomputable def DirichletSin : ℝ → ℝ :=
  fun x↦1/2 + 1/π * ∫ t in  (0).. (x), sinc t

noncomputable def HeavisidePerso (x : ℝ) : ℝ :=
  if x > 0 then 1 else if x = 0 then 1/2 else 0


def sinc_sq_times_exp (t : ℝ) : ℝ → ℝ := fun x ↦ Real.exp (-x * t) * (Real.sinc t)^2

def neg_sinc_sq_times_id_exp (t : ℝ) : ℝ → ℝ := fun x ↦ -(Real.sinc t)^2  *t* Real.exp (-x * t)

def sin_sq_times_exp (t : ℝ) : ℝ → ℝ := fun x ↦ (Real.sin t)^2 * Real.exp (-x * t)

def integral_sinc_sq_times_exp (x: ℝ) : ℝ  := ∫ t in Ioi 0 , sinc_sq_times_exp t x

def integral_neg_sinc_sq_times_id_exp (x: ℝ) : ℝ  := ∫ t in Ioi 0 , neg_sinc_sq_times_id_exp t x

def integral_sin_sq_times_exp (x: ℝ) : ℝ  := ∫ t in Ioi 0 , sin_sq_times_exp t x


lemma integrable_sinc_sq : IntegrableOn (fun (t:ℝ) ↦ (sinc t)^2) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0:ℝ) ≤ 1)] -- (0, ∞)= (0, 1] ∪ (1, ∞)
  apply IntegrableOn.union
  · -- Case 1: The function is integrable on the bounded interval (0, 1]
    -- because sinc is continuous everywhere.
    exact (continuous_sinc.pow 2).integrableOn_Ioc
  · -- Case 2: Prove integrability on (1, +∞) by comparison with t⁻²
    have h_int : IntegrableOn (fun t:ℝ ↦ t ^ (-2 : ℝ)) (Ioi 1) := by
      rw [integrableOn_Ioi_rpow_iff (zero_lt_one : 0 < (1:ℝ))]
      norm_num
    refine h_int.mono' ?_ ?_
    · -- (sinc t)² is measurable
      exact (continuous_sinc.pow 2).aestronglyMeasurable
    · -- Prove the point-wise inequality (sinc t)² ≤ t⁻² for t > 1
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi)] with t ht
      have ht₀ : t ≠ 0 := (zero_lt_one.trans (mem_Ioi.mp ht)).ne'
      simp [sinc, ht₀, div_pow, Real.rpow_neg (zero_lt_one.trans (mem_Ioi.mp ht)).le]
      field_simp[ht₀]
      gcongr
      rw [sq_le_one_iff_abs_le_one]
      exact abs_sin_le_one t

lemma deriv_sin_sq (t : ℝ) : HasDerivAt (fun x => Real.sin x ^ 2) (Real.sin (2 * t)) t := by
  have h := (Real.hasDerivAt_sin t).pow 2
  simp at h
  rw [← Real.sin_two_mul] at h
  exact h

lemma deriv_neg_inv {t : ℝ} (ht : t ≠ 0) : HasDerivAt (fun x => -1 / x) (1 / t ^ 2) t := by
  have h :=  (hasDerivAt_inv ht).neg
  field_simp at h
  have neg_inside: (-fun y:ℝ ↦ 1 / y)= (fun y:ℝ ↦ -1 / y):= by
    funext x
    simp
    field_simp
  rw[neg_inside] at h
  exact h

lemma limit_sinc_sq_mul_self_zero :
    Tendsto (fun a => (Real.sinc a)^2 * a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h_cont : ContinuousAt (fun a => (Real.sinc a)^2 * a) 0 := by
    fun_prop
  have h_lim : Tendsto (fun a => (Real.sinc a)^2 * a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_val : (Real.sinc 0)^2 * 0 = 0 := by simp
    rw [← h_val]
    apply Tendsto.mono_left
    · exact h_cont.tendsto
    · simp
      exact nhdsWithin_le_nhds
  exact h_lim

lemma limit_sinc_sq_mul_self_atTop :
    Tendsto (fun T => (Real.sinc T)^2 * T) atTop (nhds 0) := by
    -- For T > 0, we can rewrite (sinc T)^2 * T by expanding the definition of sinc
    have h_eq : ∀ᶠ T in atTop, (Real.sinc T)^2 * T = (Real.sin T)^2 / T := by
      filter_upwards [eventually_gt_atTop 0] with T hT
      unfold Real.sinc
      simp [hT.ne.symm]
      field_simp
    -- Replace the original limit goal with the simplified expression (sin T)^2 / T
    rw [tendsto_congr' h_eq]
    -- Use the Sandwich Theorem: 0 ≤ (sin T)^2 / T ≤ 1/T
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    · -- Lower bound limit: 0 → 0
      exact tendsto_const_nhds
    · -- Upper bound limit: 1/T → 0 as T → ∞
      exact tendsto_inv_atTop_zero
    · -- Proof of lower bound: (sin T)^2 / T is non-negative for T > 0
      filter_upwards [eventually_gt_atTop 0] with x hx
      positivity
    · -- Proof of upper bound: (sin T)^2 / T ≤ 1/T for T > 0
      filter_upwards [eventually_gt_atTop 0] with x hx
      field_simp
      rw [← sq_abs (Real.sin x)]
      rw[← one_pow 2]
      simp[pow_le_pow_iff_left ]
      rw[abs_le]
      constructor
      exact Real.neg_one_le_sin x
      exact Real.sin_le_one x

lemma limit_sinc_zero (T : ℝ) (hT : T > 0) :
    Tendsto (fun (a : ℝ) ↦ ∫ t in a..T, Real.sinc t) (𝓝[>] 0) (𝓝 (∫ t in 0..T, Real.sinc t)) := by
  have h_int : IntegrableOn Real.sinc (Set.uIcc 0 T) :=
    Real.continuous_sinc.integrableOn_Icc
  have h_cont := intervalIntegral.continuousOn_primitive_interval_left h_int
  apply (h_cont 0 (by simp [hT.le])).tendsto.mono_left
  rw [nhdsWithin_le_iff]
  rw [uIcc_of_le hT.le]
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with x hx_pos hx_lt
  exact ⟨hx_pos.le, hx_lt.le⟩

lemma limit_sincsq_zero (T : ℝ) (hT : T > 0) :
    Tendsto (fun (a : ℝ) ↦ ∫ t in a/2..T/2, (Real.sinc t)^2) (𝓝[>] 0) (𝓝 (∫ t in 0..T/2, (Real.sinc t)^2)) := by
  have hT2 : 0 < T / 2 := by linarith
  have h_int : IntegrableOn (fun t ↦ (Real.sinc t)^2) (uIcc 0 (T/2)) :=
    (Real.continuous_sinc.pow 2).integrableOn_Icc
  apply (intervalIntegral.continuousOn_primitive_interval_left h_int 0 left_mem_uIcc).tendsto.comp
  rw [tendsto_nhdsWithin_iff, uIcc_of_le hT2.le]
  constructor
  · convert (tendsto_id.div_const (2 : ℝ)).mono_left nhdsWithin_le_nhds
    simp
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with x hx_pos hx_lt
    simp at hx_pos hx_lt
    exact ⟨by linarith, by linarith⟩

lemma integral_sinc_sq_eq_dirichlet_bounded {a T : ℝ} (ha : 0 < a) (hT : a ≤ T) :
    (∫ t in a..T, Real.sinc t) =
    (∫ t in a/2..T/2, (Real.sinc t)^2) - (Real.sinc (a/2))^2 * (a/2) + (Real.sinc (T/2))^2 * (T/2) := by
  let a' := a / 2
  let T' := T / 2
  have ha' : 0 < a' := by dsimp [a']; linarith
  have hT' : a' ≤ T' := by dsimp[a', T']; linarith
  -- Step 1: Use a change of variables (substitution u = 2t)
  -- to relate ∫ sinc(t) to an integral involving sin(2t)/t
  have h_change_var : ∫ t in a..T, Real.sinc t = ∫ t in a'..T', Real.sin (2 * t) / t := by
    have h_sinc2 : ∀ t ∈ uIcc a' T', Real.sin (2 * t) / t = 2 * Real.sinc (2 * t) := by
      intro t ht; unfold Real.sinc; split_ifs with h0
      · rw [uIcc_of_le hT'] at ht
        simp at h0
        rw [Set.mem_Icc] at ht
        nlinarith [ha', h0]
      · field_simp
    rw [intervalIntegral.integral_congr h_sinc2]
    rw [intervalIntegral.integral_const_mul]
    -- Apply the interval version of integration by substitution: ∫ f(ct) dt
    rw [intervalIntegral.integral_comp_mul_left (fun t ↦ Real.sinc t) (c:=(2 : ℝ))]
    dsimp [a', T']
    field_simp
    simp
  -- Step 2: Use Integration by Parts (IBP) on sinc(t)^2
  -- We view (sinc t)^2 as (sin t)^2 * (1/t^2)
  -- We set u = sin(t)^2 (so u' = sin(2t)) and v' = 1/t^2 (so v = -1/t)
  have h_ibp : ∫ t in a'..T', (Real.sinc t)^2 =
      (Real.sinc a')^2 * a' - (Real.sinc T')^2 * T' + ∫ t in a'..T', Real.sin (2 * t) / t := by

    let u := fun t ↦ Real.sin t ^ 2
    let v := fun t : ℝ ↦ -1 / t
    let u' := fun t ↦ Real.sin (2 * t)
    let v' := fun t : ℝ ↦ 1 / t ^ 2
    -- Boundary term calculation: [u(t)v(t)] from a' to T'
    have h_boundary : (u T' * v T' - u a' * v a') = - (Real.sinc T')^2 * T' + (Real.sinc a')^2 * a' := by
      unfold Real.sinc; split_ifs with hT0 ha0
      · dsimp [T'] at hT0; linarith
      · dsimp [a'] at ha0; linarith
      · dsimp [T'] at hT0; linarith
      · field_simp [ha'.ne', (ha'.trans_le hT').ne']
        unfold u v
        field_simp
        ring_nf
    -- Prepare the integral for IBP by expanding the definition of sinc
    have h_prep : ∫ t in a'..T', (Real.sinc t)^2 = ∫ t in a'..T', (Real.sin t)^2 * (1 / t^2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      unfold Real.sinc
      simp
      split_ifs with h0
      · rw [uIcc_of_le hT'] at ht; rw [Set.mem_Icc] at ht; linarith [ha', h0]
      · field_simp
    rw [h_prep]
    -- Apply the Integration by Parts theorem for interval integrals
    rw[intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := u) (v := v) (u':=u') (v':=v')]
    · rw [h_boundary]
      unfold u' v
      ring_nf
      rw [intervalIntegral.integral_neg]
      ring_nf
    · -- Verify derivative of sin(t)^2 is sin(2t)
      intro t ht; exact deriv_sin_sq t
    · -- Verify derivative of -1/t is 1/t^2
      intro t ht; rw [Set.uIcc_of_le hT'] at ht; apply deriv_neg_inv; linarith [ha', ht.1]
    · -- Integrability check for the u' * v term
      apply Continuous.intervalIntegrable; fun_prop
    · -- Integrability check for the u * v' term
      apply ContinuousOn.intervalIntegrable; apply ContinuousOn.div; fun_prop; fun_prop;
      intro x hx; rw [Set.uIcc_of_le hT'] at hx; rw [Set.mem_Icc] at hx; nlinarith [ha', hx.1]

  rw [h_change_var, h_ibp]
  ring

lemma integral_sinc_zero_T (T : ℝ) (hT : T > 0) :
    (∫ t in 0..T, Real.sinc t) = (∫ t in 0..T/2, (Real.sinc t)^2) + (Real.sinc (T/2))^2 * (T/2) := by
  -- Step 1: Define the limit of the linear map x ↦ x/2 as x approach 0 from the right
  have h0 : Tendsto (fun (x:ℝ) ↦ x / 2) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    convert (tendsto_id.div_const (2:ℝ)).mono_left nhdsWithin_le_nhds
    simp
  -- Step 2: Use the uniqueness of limits to prove the equality
  -- We show that both sides of the identity are limits of the same expression as a → 0
  apply tendsto_nhds_unique (limit_sinc_zero T hT)
  apply Tendsto.congr'
  · -- Left side: The limit of the integral from a to T is the integral from 0 to T
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)]
    with a ha_pos ha_lt using (integral_sinc_sq_eq_dirichlet_bounded ha_pos ha_lt.le).symm
  · -- Right side: Evaluate the limit of the boundary terms and the squared integral
    -- As a → 0, sinc(a/2)² * (a/2) → 1² * 0 = 0
    convert (limit_sincsq_zero T hT).sub (by
      simpa using ((continuous_sinc.tendsto 0).comp h0).pow 2 |>.mul h0
    ) |>.add_const _
    simp

lemma hasDeriv_sinc_sq_times_exp (t : ℝ) (ht : 0 < t) :
    ∀ a : ℝ, HasDerivAt (sinc_sq_times_exp t) (neg_sinc_sq_times_id_exp t a) a := by
  intro a
  unfold sinc_sq_times_exp neg_sinc_sq_times_id_exp
  exact ((hasDerivAt_id a).neg.mul_const t).exp.mul_const _ |>.congr_deriv (by simp; ring)

lemma hasDeriv_neg_sinc_sq_times_id_exp (t : ℝ) (ht : 0 < t) :
    ∀ a : ℝ, HasDerivAt (neg_sinc_sq_times_id_exp t) (sin_sq_times_exp t a) a := by
  intro a
  unfold sin_sq_times_exp neg_sinc_sq_times_id_exp
  convert ((hasDerivAt_id a).neg.mul_const t).exp.mul_const (-(Real.sinc t)^2 * t) using 1
  · funext x
    simp;ring
  · unfold Real.sinc
    simp [ht.ne'] ; field_simp

lemma neg_sinc_sq_times_id_exp_le_exp (t : ℝ) :
    ∀ x, ‖neg_sinc_sq_times_id_exp t x‖ ≤ Real.exp (-x * t) := by
  intro x
  unfold neg_sinc_sq_times_id_exp
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp]
  apply mul_le_of_le_one_left (Real.exp_pos _).le
  rw [abs_neg, abs_sq]

  by_cases h : |t| ≤ (1:ℝ)
  · have h_sinc_le_one:= (sq_le_one_iff_abs_le_one ( sinc t )).mpr (Real.abs_sinc_le_one t)
    nlinarith
  · unfold Real.sinc
    split_ifs with ht
    · push_neg at h; simp [ht]
    · push_neg at h
      field_simp [ht]
      rw [←sq_abs (a:= t) ]
      field_simp
      have h_sin_le_one:= (sq_le_one_iff_abs_le_one ( Real.sin t )).mpr (Real.abs_sin_le_one t)
      exact (h_sin_le_one).trans h.le

lemma sin_sq_times_exp_le_exp (t : ℝ) :
    ∀ x, ‖sin_sq_times_exp t x‖ ≤ Real.exp (-x * t) := by
  intro x
  unfold sin_sq_times_exp
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp,abs_sq]
  field_simp
  exact (sq_le_one_iff_abs_le_one ( Real.sin t )).mpr (Real.abs_sin_le_one t)

theorem hasDeriv_integral_sinc_sq_times_exp (x : ℝ) (hx : 0 < x) :
    HasDerivAt (integral_sinc_sq_times_exp) (integral_neg_sinc_sq_times_id_exp x) x := by
  -- Define a local radius r around x to provide a neighborhood for the derivative
  let r := x / 2
  have hr : 0 < r := by unfold r; linarith
  let bound_func := fun t => Real.exp (-r * t)
  unfold integral_sinc_sq_times_exp integral_neg_sinc_sq_times_id_exp

  -- Use the dominated convergence theorem for derivatives
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (x₀ := x) (ε := r) (ε_pos := hr)
    (F := fun x' t => sinc_sq_times_exp t x')
    (F' := fun x' t => neg_sinc_sq_times_id_exp t x')
    (bound := bound_func) ?_ ?_ ?_ ?_ ?_ ?_).2

  · -- 1. Prove that the function t ↦ F(x', t) is measurable for any x'
    apply Eventually.of_forall
    intro x'
    unfold sinc_sq_times_exp
    dsimp
    let h_exp := Real.continuous_exp.comp (continuous_mul_left (-x'))
    let h_sinc := Real.continuous_sinc.pow 2
    exact (Continuous.mul h_exp h_sinc).aestronglyMeasurable

  · -- 2. Prove the integrability of the function at the specific point x
    have h_exp_int : Integrable (fun t ↦ rexp (-x * t)) (volume.restrict (Ioi 0)) := by
      have h_neg : -x < 0 := by linarith [hx]
      exact (integrableOn_exp_mul_Ioi h_neg 0).integrable
    have h_f_meas : AEStronglyMeasurable (fun t ↦ sinc_sq_times_exp t x) (volume.restrict (Ioi 0)) := by
      unfold sinc_sq_times_exp
      let h_exp := Real.continuous_exp.comp (continuous_mul_left (-x))
      let h_sinc := Real.continuous_sinc.pow 2
      exact (Continuous.mul h_exp h_sinc).aestronglyMeasurable
    -- Use the bound sinc²(t) ≤ 1 to show integrability via the exponential function
    refine h_exp_int.mono h_f_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    unfold sinc_sq_times_exp; dsimp
    rw [abs_mul, abs_sq]
    field_simp
    exact (sq_le_one_iff_abs_le_one ( sinc t )).mpr (Real.abs_sinc_le_one t)

  · -- 3. Prove that the partial derivative F' is measurable
    exact (((Real.continuous_sinc.pow 2).neg.mul continuous_id).mul
      (Real.continuous_exp.comp (continuous_mul_left (-x)))).aestronglyMeasurable

  · -- 4. Prove the uniform domination of the derivative in a ball of radius r around x
    filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0:ℝ)))] with t ht x' hx'
    rw [Metric.mem_ball, Real.dist_eq] at hx'
    -- Ensure x' stays far enough from zero so the exponential bound remains integrable
    have hx'_r : r ≤ x' := by
      have h_dist : x - r < x' := by
        rw [abs_lt] at hx'
        linarith
      have : x - r = r := by unfold r ; linarith
      linarith
    have h_const : -x' ≤ -r := by linarith [abs_lt.mp hx']
    have ht_pos : 0 ≤ t := by
      rw [mem_Ioi] at ht
      linarith
    -- Calculation showing ‖neg_sinc_sq_times_id_exp‖ ≤ exp(-r * t)
    calc ‖neg_sinc_sq_times_id_exp t x'‖
      _ ≤ rexp (-x' * t) := neg_sinc_sq_times_id_exp_le_exp t x'
      _ ≤ rexp (-r * t)  :=  by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right h_const ht_pos

  · -- 5. Prove that the bounding function exp(-r * t) is integrable
    have h_min_r: -r<0:= by linarith
    exact (integrableOn_exp_mul_Ioi h_min_r 0).integrable

  · -- 6. Prove point-wise differentiability of the integrand for almost every t
    filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0:ℝ) ))] with t ht x' _
    have ht_gt0 : 0 < t := by
      rw [mem_Ioi] at ht
      exact ht
    exact hasDeriv_sinc_sq_times_exp t ht_gt0 x'

theorem hasDeriv_integral_neg_sinc_sq_times_id_exp (x : ℝ) (hx : 0 < x) :
    HasDerivAt (integral_neg_sinc_sq_times_id_exp) (integral_sin_sq_times_exp x) x := by
  -- Define a local radius r around x to provide a neighborhood for the derivative
  let r := x / 2
  have hr : 0 < r := by unfold r; linarith
  unfold integral_neg_sinc_sq_times_id_exp integral_sin_sq_times_exp
  -- The bounding function for the derivative is again a decaying exponential
  let bound_func := fun t => Real.exp (-r * t)

  -- Use the dominated convergence theorem for derivatives
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (x₀ := x) (ε := r) (ε_pos := hr)
    (F := fun x' t => neg_sinc_sq_times_id_exp t x')
    (F' := fun x' t => sin_sq_times_exp t x')
    (bound := bound_func) ?_ ?_ ?_ ?_ ?_ ?_).2

  · -- 1. Prove the integrand F is measurable for all x' in the neighborhood
    apply Eventually.of_forall; intro x'
    let h_sinc := Continuous.mul (Real.continuous_sinc.pow 2).neg continuous_id
    let h_exp := Real.continuous_exp.comp (continuous_mul_left (-x'))
    exact (Continuous.mul h_sinc h_exp).aestronglyMeasurable

  · -- 2. Prove the integrand F is integrable at the point x
    have h_exp_int : Integrable (fun t ↦ rexp (-x * t)) (volume.restrict (Ioi 0)) := by
      have h_neg : -x < 0 := by linarith [hx]
      exact (integrableOn_exp_mul_Ioi h_neg 0).integrable
    have h_f_meas : AEStronglyMeasurable (fun t ↦ neg_sinc_sq_times_id_exp t x) (volume.restrict (Ioi 0)) := by
      let f_trig := (Real.continuous_sinc.pow 2).neg.mul continuous_id
      let f_exp := Real.continuous_exp.comp (continuous_mul_left (-x))
      exact (Continuous.mul f_trig f_exp).aestronglyMeasurable
    -- Use the previously established bound |t * sinc²(t) * e⁻ˣᵗ| ≤ e⁻ˣᵗ
    refine h_exp_int.mono h_f_meas ?_
    filter_upwards with t
    rw [norm_eq_abs (r:= rexp (-x * t)), Real.abs_exp]
    exact neg_sinc_sq_times_id_exp_le_exp t x

  · -- 3. Prove the partial derivative F' is measurable
    let h_sin := Real.continuous_sin.pow 2
    let h_exp := Real.continuous_exp.comp (continuous_mul_left (-x))
    exact (Continuous.mul h_sin h_exp).aestronglyMeasurable

  · -- 4. Dominate the derivative F' = sin²(t)e⁻ˣ'ᵗ by the integrable function exp(-rt)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x' hx'
    rw [Metric.mem_ball, Real.dist_eq] at hx'
    -- Since sin²(t) ≤ 1, |sin²(t)e⁻ˣ'ᵗ| ≤ e⁻ˣ'ᵗ. We then bound x' by r.
    refine (sin_sq_times_exp_le_exp t x').trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (mem_Ioi.mp ht).le))
    have h_dist : x - r < x' := by
      rw [abs_lt] at hx'
      linarith
    have : x - r = r := by unfold r ; linarith
    linarith [abs_lt.mp hx']

  · -- 5. The bounding function exp(-rt) is integrable on (0, ∞)
    exact (integrableOn_exp_mul_Ioi (by linarith) 0)

  · -- 6. Point-wise derivative: ∂/∂x' (-t * sinc²(t) * e⁻ˣ'ᵗ) = sin²(t) * e⁻ˣ'ᵗ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x' _
    exact hasDeriv_neg_sinc_sq_times_id_exp t (mem_Ioi.mp ht) x'

lemma integrable_cexp_mul_Ioi_of_re_neg {z : ℂ} (hz : z.re < 0) (ε : ℝ) :
    Integrable (fun (t : ℝ) => cexp (↑t * z)) (volume.restrict (Ioi ε)) := by
  rw [← integrable_norm_iff]
  simp_rw [Complex.norm_exp]
  have : (fun t:ℝ ↦ (rexp ((↑t * z).re))) = (fun (t:ℝ) ↦ rexp ( (z.re) * t)) := by
    funext t
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_comm]

  rw [this]
  exact integrableOn_exp_mul_Ioi hz ε
  apply Continuous.aestronglyMeasurable
  continuity

lemma add_integral_integrable(ε : ℝ)(x : ℝ) (hx : 0 < x)  :
 ∫ t in Ioi ε, (cexp (-↑t*(2*I + x))+ cexp ( ↑t*(2*I -x )) -2*cexp (- ↑t*x))=
 (∫ t in Ioi ε, cexp (-↑t*(2*I + x)))+ (∫ t in Ioi ε,cexp ( ↑t*(2*I -x ))) -∫ t in Ioi ε,(2*cexp (- ↑t*x)):= by

  have h1 : Integrable (fun t ↦ cexp (-↑t * (2 * I + x))) (volume.restrict (Ioi ε)) := by
    convert integrable_cexp_mul_Ioi_of_re_neg (ε := ε) (by simp [hx] : (-2*I - x).re < 0) using 1
    ext; ring_nf

  have h2 : Integrable (fun t ↦ cexp (↑t * (2 * I - x))) (volume.restrict (Ioi ε)) := by
    apply integrable_cexp_mul_Ioi_of_re_neg
    simp [hx]

  have h3 : Integrable (fun (t:ℝ) ↦ 2 * cexp (-↑t * x)) (volume.restrict (Ioi ε)) := by
    apply Integrable.const_mul
    convert integrable_cexp_mul_Ioi_of_re_neg (ε := ε) (by simp [hx] : (-x : ℂ).re < 0) using 1
    ext; ring_nf
  convert integral_sub (h1.add h2) h3 using 1
  simp_rw [Pi.add_apply]
  congr 1
  rw [integral_add h1 h2]

theorem compute_deriv_integral_sin_div_times_exp_eps(ε : ℝ)(x : ℝ) (hx : 0 < x) :
 ∫ t in Ioi ε, (Real.sin t)^2 * Real.exp (-x * t)=rexp (- x* ε)*((Real.sin (2 * ε)- (x/2) * Real.cos (2 * ε)) / (4 + x^2)+ 1 / (2 * x)) :=by
  let F (t : ℝ) := rexp (-x * t) * (2 * Real.sin (2 * t) - x * Real.cos (2 * t)) / (x^2 + 4)
  have h_exp : IntegrableOn (fun t ↦ rexp (-x * t)) (Ioi ε) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hx) ε

  have h_cos : ∫ t in Ioi ε, Real.cos (2 * t) * rexp (-x * t) =
      rexp (-x * ε) * (x * Real.cos (2 * ε) - 2 * Real.sin (2 * ε)) / (x^2 + 4) := by

    have h_eq : rexp (-x * ε) * (x * Real.cos (2 * ε) - 2 * Real.sin (2 * ε)) / (x^2 + 4) = 0 - F ε := by
      dsimp [F]
      ring
    rw [h_eq]
    apply integral_Ioi_of_hasDerivAt_of_tendsto (f := F) (m := 0)
    · dsimp [F]
      apply Continuous.continuousOn
      apply Continuous.div_const
      apply Continuous.mul
      · exact Continuous.rexp (continuous_mul_left _)
      · apply Continuous.sub <;> apply Continuous.mul <;> try exact continuous_const
        · continuity
        · continuity
      · exact left_mem_Ici
    · intro t _
      dsimp [F]
      convert HasDerivAt.mul (((hasDerivAt_id t).const_mul (-x)).exp) ((((hasDerivAt_id t).const_mul 2).sin.const_mul 2 |>.sub (((hasDerivAt_id t).const_mul 2).cos.const_mul x)).div_const (x^2 + 4))
      using 1
      · ext x; dsimp; field_simp
      · dsimp; field_simp;ring_nf
    · apply Integrable.mono h_exp
      · exact (Real.continuous_cos.comp (continuous_mul_left 2)).mul (continuous_mul_left (-x)).rexp |>.aestronglyMeasurable
      · refine ae_of_all _ (fun t ↦ ?_)
        simp [field, Real.abs_cos_le_one]
    · have h_rew : (fun t ↦ F t) = (fun t ↦ (2 * Real.sin (2 * t) - x * Real.cos (2 * t)) / (x ^ 2 + 4) * rexp (-x * t)) := by
        ext t; dsimp [F]; ring
      simp[h_rew]
      apply bdd_le_mul_tendsto_zero' ((2 + |x|) / (x ^ 2 + 4))
      · filter_upwards with t
        rw [abs_div, abs_of_pos (a:= x^2+ 4) (by nlinarith)]
        field_simp
        calc |2 * Real.sin (2 * t) - x * Real.cos (2 * t)|
        _ ≤ |2 * Real.sin (2 * t)| + |x * Real.cos (2 * t)| := abs_sub _ _
        _ ≤ 2 * 1 + |x| * 1 := add_le_add (by simp [abs_sin_le_one]) (by simp; field_simp[hx]; simp[abs_cos_le_one])
        _ = 2 + |x| := by ring
      · exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hx)

  simp_rw [Real.sin_sq, sub_mul, div_mul_eq_mul_div, one_mul]
  rw [integral_sub]
  rotate_left
  · exact h_exp
  · apply Integrable.mono h_exp
    · exact ((Real.continuous_cos.pow 2).mul (continuous_exp.comp (continuous_mul_left (-x)))).aestronglyMeasurable
    · refine ae_of_all _ (fun t ↦ ?_)
      simp [field, Real.abs_cos_le_one]
  simp_rw [Real.cos_sq, div_eq_mul_inv, add_mul, mul_assoc]
  simp_rw[one_mul]
  rw [integral_add]
  rotate_left
  · apply Integrable.const_mul (c:=2⁻¹); exact h_exp
  · apply Integrable.mono h_exp
    · exact ((Real.continuous_cos.comp (continuous_mul_left 2)).mul (continuous_const.mul (continuous_exp.comp (continuous_mul_left (-x))))).aestronglyMeasurable
    · refine ae_of_all _ (fun t ↦ ?_)
      simp [field]
      exact (Real.abs_cos_le_one (2 * t)).trans (by linarith)

  rw [integral_const_mul]
  have h_pull : ∫ a in Ioi ε, Real.cos (2 * a) * (2⁻¹ * rexp (-x * a)) =
      2⁻¹ * ∫ a in Ioi ε, Real.cos (2 * a) * rexp (-x * a) := by
    rw [←integral_const_mul]
    congr 1
    funext a
    field_simp
  rw[h_pull,h_cos,integral_exp_mul_Ioi (by linarith[hx]) ε]
  field_simp [hx.ne.symm]
  ring_nf

theorem hasDeriv_integral_neg_sinc_sq_times_id_exp' (x : ℝ) (hx : 0 < x) : HasDerivAt (integral_neg_sinc_sq_times_id_exp) (-(1/2) * x / (4 + x^2)+ 1 / (2 * x)) x:= by
  have h_deriv: HasDerivAt (integral_neg_sinc_sq_times_id_exp) (integral_sin_sq_times_exp x) x := by
    exact hasDeriv_integral_neg_sinc_sq_times_id_exp x hx
  unfold integral_sin_sq_times_exp at h_deriv
  unfold sin_sq_times_exp at h_deriv
  simp_rw[compute_deriv_integral_sin_div_times_exp_eps 0 x hx] at h_deriv
  simp at h_deriv
  have:-(x / 2) / (4 + x ^ 2) + x⁻¹ * 2⁻¹= -(1/2) * x / (4 + x^2)+ 1 / (2 * x):= by
    field_simp
  rw[this] at h_deriv
  exact h_deriv

lemma tendsto_integral_neg_sinc_sq_times_id_exp :
    Tendsto integral_neg_sinc_sq_times_id_exp atTop (𝓝 0) := by
  unfold integral_neg_sinc_sq_times_id_exp neg_sinc_sq_times_id_exp
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_inv_atTop_zero ?_ ?_
  · filter_upwards with x using norm_nonneg _
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have : x⁻¹ = ∫ t in Ioi 0, rexp (-x * t) := by
      rw[integral_exp_mul_Ioi (neg_neg_of_pos hx) 0];simp
    rw [this]
    refine norm_integral_le_of_norm_le (integrableOn_exp_mul_Ioi (neg_neg_of_pos hx) 0) ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0:ℝ)))] with t ht
    rw [norm_mul, norm_mul, norm_neg, norm_pow, norm_eq_abs, norm_eq_abs, norm_eq_abs, Real.abs_exp]
    field_simp
    by_cases h : |t| ≤ (1:ℝ)
    · exact mul_le_one₀ (pow_le_one₀ (n:=2) (abs_nonneg _) (Real.abs_sinc_le_one t)) ((abs_nonneg t)) h
    · have ht_pos : 0 < t := mem_Ioi.mp ht
      have ht_ne : t ≠ 0 := ht_pos.ne'
      rw [abs_of_pos ht_pos] at h; push_neg at h ;rw [abs_of_pos ht_pos]
      unfold sinc
      simp[ht_ne] ; field_simp
      exact (Real.sin_sq_le_one t).trans h.le

lemma tendsto_integral_sinc_sq_times_exp :
  Tendsto integral_sinc_sq_times_exp atTop (𝓝 0) := by
  unfold integral_sinc_sq_times_exp sinc_sq_times_exp
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_inv_atTop_zero (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have : x⁻¹ = ∫ t in Ioi 0, rexp (-x * t) := by
      rw[integral_exp_mul_Ioi (neg_neg_of_pos hx) 0];simp
  rw [this]
  refine norm_integral_le_of_norm_le (integrableOn_exp_mul_Ioi (neg_neg_of_pos hx) 0) ?_
  filter_upwards
  intro a
  rw [norm_mul, norm_pow, norm_eq_abs,norm_eq_abs, Real.abs_exp]
  field_simp
  exact pow_le_one₀ (n:=2) (abs_nonneg _) (Real.abs_sinc_le_one a)

theorem integral_neg_sinc_sq_times_id_exp_eq (x : ℝ) (hx : 0 < x) :
    integral_neg_sinc_sq_times_id_exp x = 1/4 * Real.log (x^2 / (4 + x^2)) := by
  -- Define the target logarithmic function G and the difference function 'diff'
  let G := fun t ↦ 1/4 * (Real.log (t^2) - Real.log (4 + t^2))
  let diff := fun t ↦ integral_neg_sinc_sq_times_id_exp t - G t

  -- Step 1: Calculate the derivative of G
  have hG : ∀ y ∈ Ioi 0, HasDerivAt G (1 / (2 * y) - y / (2 * (4 + y^2))) y := by
    intro y hy
    have y_pos : 0 < y := mem_Ioi.mp hy
    apply HasDerivAt.congr_deriv (f' := 1/(2*y) - y/(2*(4+y^2)))
    · unfold G; simp_rw [mul_sub]
      apply HasDerivAt.sub
      · -- Differentiate 1/4 * log(y²) = 1/2 * log(y)
        convert (HasDerivAt.log (hasDerivAt_id y) y_pos.ne').const_mul (1/2) using 1
        · funext a ; rw[log_pow];rw [Nat.cast_ofNat]; simp only [id_eq]
          by_cases h : Real.log a = 0
          · rw [h]; simp
          · field_simp
            ring
        · simp only [id_eq]; field_simp
      · -- Differentiate 1/4 * log(4 + y²)
        convert (HasDerivAt.log (HasDerivAt.const_add 4 (hasDerivAt_pow 2 y)) (by positivity)).const_mul (1/4) using 1; field_simp; ring
    · field_simp

  -- Step 2: Show the derivative of (Integral - G) is zero
  -- This implies the function is constant on (0, ∞)
  have h_deriv_zero : ∀ y ∈ Ioi 0, HasDerivAt diff 0 y := by
    intro y hy
    have y_pos : 0 < y := mem_Ioi.mp hy
    -- Use the previously proven derivative of the integral
    have h_int := hasDeriv_integral_neg_sinc_sq_times_id_exp' y y_pos
    convert h_int.sub (hG y hy) using 1; field_simp; ring

  -- Step 3: Show that G(y) tends to 0 as y → ∞
  have h_lim_zero : Tendsto diff atTop (𝓝 0) := by
    rw [← sub_zero (0 : ℝ)]
    -- We already know the integral part tends to zero
    apply Tendsto.sub tendsto_integral_neg_sinc_sq_times_id_exp
    have hG_lim : Tendsto G atTop (𝓝 0) := by
      -- Rewrite log(y²) - log(4 + y²) as log(y² / (4 + y²))
      refine (tendsto_congr' ( f₁:= fun t ↦ 1/4 * Real.log (t^2 / (4 + t^2))) (f₂:=G) ?_).mp ?_
      · filter_upwards [eventually_gt_atTop 0] with t ht
        rw [Real.log_div (pow_ne_zero 2 ht.ne') (by positivity)]
      -- Show the argument of the log tends to 1
      refine (tendsto_congr' (f₁ := fun t ↦ 1/4 * Real.log (1 / (4 / t^2 + 1))) ?_).mp ?_
      · filter_upwards [eventually_gt_atTop 0] with t ht
        field_simp [ht.ne']
      rw [show (0 : ℝ) = 1/4 * Real.log 1 by simp]
      apply Tendsto.const_mul
      apply (continuousAt_log (by norm_num)).tendsto.comp
      -- Show 1 / (4/t² + 1) → 1 as t → ∞
      have h_frac : Tendsto (fun t:ℝ ↦ 1 / (4 / t^2 + 1)) atTop (𝓝 1) := by
        have : (fun t ↦ 1 / (4 / t^2 + 1)) = (fun _ ↦ (1 : ℝ)) / (fun t ↦ 4 / t^2 + 1) := by
            rfl
        rw[this]
        convert Tendsto.div (tendsto_const_nhds (x := 1)) ?hg (show (1 : ℝ) ≠ 0 by norm_num)
        · field_simp
        · convert Tendsto.add (Filter.Tendsto.div_atTop (tendsto_const_nhds (x := (4:ℝ))) (tendsto_pow_atTop (n:= 2) (by norm_num))) (tendsto_const_nhds (x := 1))
          ring_nf
      exact h_frac
    exact hG_lim

  -- Step 4: Use the constant function theorem
  -- Since the derivative is zero and the limit at infinity is zero, the function is zero everywhere
  have h_deriv_zero' : EqOn (deriv diff) 0 (Set.Ioi 0) := by
    intro y hy
    have h := h_deriv_zero y hy
    simpa using h.deriv
  have h_Diffdiff: DifferentiableOn ℝ diff (Set.Ioi 0) := by
    intro y hy
    exact (h_deriv_zero y hy).differentiableAt.differentiableWithinAt

  -- Topology prerequisites for the constant function theorem
  have hIoi_open : IsOpen (Set.Ioi (0 : ℝ)) :=
    isOpen_Ioi
  have hIoi_preconnected : IsPreconnected (Set.Ioi (0 : ℝ)) :=
    isPreconnected_Ioi

  -- The function is constant on the interval
  have h_const : ∀ y ∈ Ioi 0, diff y = diff x :=
    fun y hy ↦ IsOpen.is_const_of_deriv_eq_zero hIoi_open hIoi_preconnected h_Diffdiff h_deriv_zero' hy hx
  -- Since it's constant and tends to 0, it must be 0
  have h_is_zero : diff x = 0 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h_lim_zero
    filter_upwards [eventually_gt_atTop 0] with y hy
    exact (h_const y (mem_Ioi.mpr hy)).symm

  -- Final cleanup: Expand definitions back to the goal form
  unfold diff G at h_is_zero
  rw [Real.log_div (pow_ne_zero 2 hx.ne') (by positivity)]
  exact sub_eq_zero.mp h_is_zero

lemma hasDeriv_integral_sinc_sq_times_exp'(x : ℝ) (hx : 0 < x) : HasDerivAt (integral_sinc_sq_times_exp ) (1/4 * Real.log (x^2/(4+x^2))) x := by
  have h_deriv: HasDerivAt (integral_sinc_sq_times_exp) (integral_neg_sinc_sq_times_id_exp x) x := by
    exact hasDeriv_integral_sinc_sq_times_exp x hx
  have h_deriv_eq:integral_neg_sinc_sq_times_id_exp x = 1/4*Real.log (x^2/(4+x^2)):= integral_neg_sinc_sq_times_id_exp_eq x hx
  rw[h_deriv_eq] at h_deriv
  exact h_deriv

lemma h_log_ineq_neg1 : ∀ y, -1/2 < y → y ≤ 0 → Real.log (1 + y) ≤ y - y^2 / 2 := by
  intro y hy_gt hy_le
  let f := fun t ↦ Real.log (1 +t) - t + t^2 / 2
  have h_deriv : ∀ x ∈ Set.Icc y 0, HasDerivAt f (x^2 / (1 + x)) x := by
    intro x hx
    have : 0 < 1 + x := by linarith [hx.1]
    have h_neq:  1 + id x ≠ 0:= by
      simp
      linarith
    unfold f
    convert (HasDerivAt.sub
    (HasDerivAt.log (hasDerivAt_id x |>.const_add 1) h_neq)
    (hasDerivAt_id x)).add ((hasDerivAt_id x).pow 2 |>.div_const 2) using 1
    simp
    field_simp
    ring_nf
  have hfy : f y ≤ 0 := by
    have hf0 : f 0 = 0 := by
      simp [f]
    rw [← hf0]
    have h_mono : MonotoneOn f (Icc y 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc y 0)
      · apply ContinuousOn.add
        · apply ContinuousOn.sub
          · apply ContinuousOn.log
            refine Continuous.continuousOn ?_
            continuity
            intro z hz; linarith [hy_gt, hz.1]
          · exact continuousOn_id
        · refine Continuous.continuousOn ?_
          continuity
      · intro x hx
        have hx_mem : x ∈ Icc y 0 := by
          rw [interior_Icc] at hx
          exact Ioo_subset_Icc_self hx
        exact (h_deriv x hx_mem).differentiableAt.differentiableWithinAt
      · intro u hu
        have hu_mem : u ∈ Icc y 0 := by
          rw [interior_Icc] at hu
          exact Ioo_subset_Icc_self hu
        rw [(h_deriv u hu_mem).deriv]
        have hu_gt_neg1 : -1/2 < u := by
          rw [interior_Icc] at hu
          linarith [hy_gt, hu.1]
        have h_den : 0 < 1 + u := by linarith  [hu_gt_neg1]
        have h_pos : 0 ≤ u^2 / (1 + u) := by
          positivity
        exact h_pos
    apply h_mono
    · exact left_mem_Icc.mpr hy_le
    · exact right_mem_Icc.mpr hy_le
    · exact hy_le
  unfold f at hfy
  linarith

lemma h_log_ineq_neg2 : ∀ y, -1<y → y <0 → Real.log (1 + y)/y ≤ 1/(1+y) := by
  intro y hy_gt hy_lt

  let f := fun t ↦ t  / (1+t)-Real.log (1 +t)
  have h_deriv : ∀ x ∈ Set.Icc y 0, HasDerivAt f  ( 1/(1+x)^2-1/(1+x) ) x := by
    intro x hx

    have : 0 < 1 + x := by linarith [hx.1]
    have h_neq:  1 + id x ≠ 0:= by
      simp
      linarith
    unfold f
    apply HasDerivAt.sub
    · have h_u : HasDerivAt (fun t ↦ t) 1 x := hasDerivAt_id x
      have h_v : HasDerivAt (fun t ↦ 1 + t) 1 x := by
        convert (hasDerivAt_const x 1).add (hasDerivAt_id x)
        simp
      have h_div := HasDerivAt.div h_u h_v (by linarith)
      field_simp at h_div
      have :  (1:ℝ) + x -x = (1:ℝ):= by
        ring_nf
      rw[this] at h_div
      convert h_div using 1
    · let f:= fun t:ℝ ↦ 1+t
      let f':= fun t:ℝ ↦ (1:ℝ)
      have hx_pos : f x ≠ 0 := by
        unfold f
        linarith[hx.left, hy_gt]
      have derivf: HasDerivAt f ((0:ℝ)+ (1:ℝ)) x:= by
        unfold f
        apply HasDerivAt.add
        · exact hasDerivAt_const x 1
        · exact hasDerivAt_id x
      have: (0:ℝ)+ 1=f' x:= by
        unfold f'
        simp
      rw[this] at derivf
      have h_log : HasDerivAt (fun t ↦ Real.log (1 + t)) (1 / (1 + x)) x := by
        let h:=HasDerivAt.log derivf hx_pos
        unfold f f' at h
        exact h
      exact h_log

  have hfy : f y ≤  0 := by
    have hf0 : f 0 = 0 := by
      simp [f]
    rw [← hf0]
    have h_mono : MonotoneOn f (Icc y 0) := by
      unfold f
      apply monotoneOn_of_deriv_nonneg (convex_Icc y 0)
      · apply ContinuousOn.add
        · apply ContinuousOn.div
          · exact continuousOn_id
          · refine Continuous.continuousOn ?_
            continuity
          · intro x hx
            have hx_low : y ≤ x := (mem_Icc.mp hx).1
            have hx_gt_neg1 : -1 < x := lt_of_lt_of_le hy_gt hx_low
            linarith
        · apply ContinuousOn.neg
          apply ContinuousOn.log
          refine Continuous.continuousOn ?_
          continuity
          intro x hx
          have hx_low : y ≤ x := (mem_Icc.mp hx).1
          have hx_gt_neg1 : -1 < x := lt_of_lt_of_le hy_gt hx_low
          linarith

      · intro x hx
        have hx_mem : x ∈ Icc y 0 := by
          rw [interior_Icc] at hx
          exact Ioo_subset_Icc_self hx
        exact (h_deriv x hx_mem).differentiableAt.differentiableWithinAt
      · intro u hu
        have hu_mem : u ∈ Icc y 0 := by
          rw [interior_Icc] at hu
          exact Ioo_subset_Icc_self hu
        rw [(h_deriv u hu_mem).deriv]
        have hu_gt_neg1 : -1 < u := by
          rw [interior_Icc] at hu
          have:= hu.1
          linarith
        have h_den : 0 < 1 + u := by linarith  [hu_gt_neg1]
        field_simp [h_den.ne']
        ring_nf
        rw [interior_Icc] at hu
        have := hu.2
        linarith
    apply h_mono
    · exact left_mem_Icc.mpr hy_lt.le
    · exact right_mem_Icc.mpr hy_lt.le
    exact hy_lt.le
  unfold f at hfy
  have h_rw:  (y:ℝ)  / (1 + y) ≤ Real.log (1 + y) := by linarith
  have: (y:ℝ )/ (1 + y)=y * (1/(1 + y)):=by
    field_simp
  rw[this] at h_rw
  have h_div := (div_le_iff_of_neg'  (a:= 1/(1 + y)) (b:=Real.log (1 + y))  hy_lt).mpr h_rw
  exact h_div

theorem integral_sinc_sq_times_exp_eq (x : ℝ) (hx : 0 < x) :
    integral_sinc_sq_times_exp x = x/4 * Real.log (x^2/(4+x^2)) + Real.arctan (2/x) := by
  -- Define the candidate function G and the difference function 'diff'
  let G := fun t ↦ t/4 * Real.log (t^2/(4+t^2)) + Real.arctan (2/t)
  let diff := fun t ↦ integral_sinc_sq_times_exp t - G t

  -- Step 1: Verify the derivative of the candidate function G
  -- We want to show that dG/dt matches the previously computed derivative of our integral
  have hG : ∀ y ∈ Ioi 0, HasDerivAt G (1/4 * Real.log (y^2 / (4 + y^2))) y := by
    intro y hy
    have y_pos : 0 < y := mem_Ioi.mp hy
    have den_ne : 4 + y^2 ≠ 0 := by nlinarith
    unfold G
    -- Use derivative rules for product (t * log), composition (log of fraction), and arctan(2/t)
    convert (HasDerivAt.mul ((hasDerivAt_id y).div_const 4) (HasDerivAt.log ?_ ?_)).add (HasDerivAt.arctan ?_) using 1
    rotate_left; rotate_left
    · apply HasDerivAt.div
      · apply HasDerivAt.pow (n:=2) (hasDerivAt_id y)
      · apply HasDerivAt.const_add; apply HasDerivAt.pow (n:=2) (hasDerivAt_id y)
      · nlinarith
    · positivity[y_pos, den_ne]
    rotate_left
    · -- Derivative of arctan(2/y) which involves the chain rule on 2/y
      convert (hasDerivAt_inv y_pos.ne').const_mul 2 using 1
    -- Algebraic simplification to show the sum reduces to the log term only
    dsimp; field_simp ; ring_nf

  -- Step 2: Show that 'diff' is a constant function
  -- Since deriv(integral) = hG, then deriv(diff) = 0
  have h_deriv_zero : ∀ y ∈ Ioi 0, HasDerivAt diff 0 y := by
    intro y hy
    convert (hasDeriv_integral_sinc_sq_times_exp' y hy).sub (hG y hy) using 1; simp

  -- Step 3: Handle the limit at infinity to determine the constant
  -- we show that both terms → 0 as t → ∞
  have h_lim_zero : Tendsto diff atTop (𝓝 0) := by
    rw [← sub_zero (0 : ℝ)]
    apply Tendsto.sub tendsto_integral_sinc_sq_times_exp
    have hG_lim : Tendsto G atTop (𝓝 0) := by
      unfold G
      rw [show (0 : ℝ) = 0 + 0 by simp]
      apply Tendsto.add
      · -- Limit of the term t/4 * log(...)
        -- We use an auxiliary variable u = -4/(4+t²) which tends to 0
        let u := fun t:ℝ ↦ -4 / (4 + t^2)
        have h_u : Tendsto u atTop (𝓝 0) := by
          apply tendsto_const_nhds.div_atTop; apply tendsto_const_nhds.add_atTop; exact tendsto_pow_atTop (by norm_num)
        -- Rewrite the expression to use the limit log(1+u)/u → 1
        have h_equiv : (fun t ↦ t / 4 * Real.log (t^2 / (4 + t^2))) =
                     (fun t ↦ (t * (-4 / (4 + t^2)) / 4) * (Real.log (1 + u t) / u t)) := by
            ext t ; unfold u ;field_simp ; ring_nf
        rw [h_equiv]
        rw [show (0 : ℝ) = 0 * 1 by simp]
        apply Tendsto.mul
        · -- The first part: t * u / 4 → 0: we use the Sandwich theorem
          apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun (x:ℝ) ↦ -1/x) (h := fun (x:ℝ) ↦ 0)
          · simpa using (tendsto_const_nhds (x := (-1 : ℝ))).div_atTop tendsto_id
          · exact tendsto_const_nhds
          · filter_upwards [eventually_gt_atTop 0] with x hx; field_simp; nlinarith
          · filter_upwards [eventually_gt_atTop 0] with x hx; field_simp; nlinarith
        · -- The second part: log(1+u)/u → 1
          -- This uses again the Sandwich theorem
          -- with the logarithmic inequalities h_log_ineq_neg1 and h_log_ineq_neg2
          apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun x ↦ 1 - u x / 2) (h := fun x ↦ 1 / (1 + u x))
          · simpa [h_u] using h_u.mul_const (-(1/2 : ℝ)) |>.const_add 1
          · simpa [h_u] using (h_u.const_add (1 : ℝ)).inv₀ (by norm_num)
          · -- Applying h_log_ineq_neg1
            filter_upwards [h_u.eventually (eventually_gt_nhds (by norm_num : (-1/2 : ℝ) < 0)),
                eventually_gt_atTop (0 : ℝ)] with x h_gt h_pos
            have h_lt : u x < 0 := by unfold u; exact div_neg_of_neg_of_pos (by norm_num) (by nlinarith)
            rw [le_div_iff_of_neg h_lt]
            linarith [h_log_ineq_neg1 (u x) h_gt h_lt.le]
          · -- Applying h_log_ineq_neg2
            filter_upwards [h_u.eventually (eventually_gt_nhds (by norm_num : (-1: ℝ) < 0)),
                  eventually_gt_atTop (0 : ℝ)] with x h_gt h_pos
            have h_lt : u x < 0 := by unfold u; exact div_neg_of_neg_of_pos (by norm_num) (by nlinarith)
            exact h_log_ineq_neg2 (u x) h_gt h_lt
      · -- Limit of arctan(2/t) → arctan(0) = 0
        simpa using Real.continuous_arctan.continuousAt.tendsto.comp (tendsto_const_nhds.div_atTop tendsto_id)
    exact hG_lim

  -- Step 4: Combine zero derivative and vanishing limit
  -- Since the function is constant on (0, ∞) and tends to 0, it is zero everywhere
  have h_const : ∀ y ∈ Ioi 0, diff y = diff x :=
    fun y hy ↦ IsOpen.is_const_of_deriv_eq_zero isOpen_Ioi isPreconnected_Ioi
      (fun z hz ↦ (h_deriv_zero z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (h_deriv_zero z hz).deriv) hy hx

  have h_is_zero : diff x = 0 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h_lim_zero
    filter_upwards [eventually_gt_atTop 0] with y hy
    exact (h_const y hy).symm

  -- Step 5: Final conclusion
  exact sub_eq_zero.mp h_is_zero

theorem integral_sinc_sq_eq_pi_div_two : ∫ t in Ioi 0, (Real.sinc t)^2 = π / 2 := by

  -- Step 1: Use the Dominated Convergence Theorem (DCT) to show that
  -- as x → 0⁺, ∫ sinc²(t) e⁻ˣᵗ dt converges to the target integral ∫ sinc²(t) dt
  have h_lim_int : Tendsto (fun x => integral_sinc_sq_times_exp x) (𝓝[>] 0) (𝓝 (∫ t in Ioi 0, (Real.sinc t)^2)) := by
    -- Dominating function is sinc²(t), which we already proved is integrable.
    refine tendsto_integral_filter_of_dominated_convergence (fun t => (Real.sinc t)^2) ?_ ?_ integrable_sinc_sq ?_
    · -- Measurability of the family of functions
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id') |>.mul (Real.continuous_sinc.pow 2)).aestronglyMeasurable
    · -- Domination: |sinc²(t) * exp(-xt)| ≤ sinc²(t) for x > 0 and t > 0
      filter_upwards [self_mem_nhdsWithin] with x hx
      unfold sinc_sq_times_exp
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ (fun t (ht : 0 < t) ↦ ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (exp_pos _).le, abs_of_nonneg (sq_nonneg (Real.sinc t))]
      refine mul_le_of_le_one_left (sq_nonneg _) ?_
      rw [exp_le_one_iff]
      replace hx : 0 < x := hx
      nlinarith
    · -- Point-wise convergence: exp(-xt) → 1 as x → 0, so the integrand converges to sinc²(t)
      unfold sinc_sq_times_exp
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ (fun t (ht : 0 < t) ↦ ?_)
      have h_cont : Continuous (fun n ↦ rexp (-n * t) * Real.sinc t ^ 2) := by continuity
      simpa using (h_cont.tendsto 0).mono_left nhdsWithin_le_nhds

  -- Step 2: Use the analytical expression x/4 * log(x²/(4+x²)) + arctan(2/x)
  -- to compute the limit as x → 0⁺.
  have h_lim_int2 : Tendsto (fun x ↦ integral_sinc_sq_times_exp x) (𝓝[>] 0) (𝓝 (π / 2)) := by
    -- Replace the integral with the analytical formula proven in integral_sinc_sq_times_exp_eq
    refine (tendsto_congr' (f₁ := integral_sinc_sq_times_exp)
      (f₂ := fun x ↦ (x / 4) * Real.log (x^2 / (4 + x^2)) + Real.arctan (2 / x)) ?_).mpr ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx using integral_sinc_sq_times_exp_eq x hx
    · -- The limit of the sum is 0 + π/2
      rw [show (π / 2 : ℝ) = 0 + π / 2 by simp]
      apply Tendsto.add
      · -- Limit of the term (x/4) * log(x² / (4+x²)) as x → 0⁺
        refine (tendsto_congr' (f₂ := fun x ↦ (1/2) * (x * Real.log x) - (x/4) * Real.log (4 + x^2)) ?_).mpr ?_
        · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
          rw [Real.log_div (pow_ne_zero 2 hx.ne') (by positivity), Real.log_pow]; ring
        · rw [show (0 : ℝ) = (1/2) * 0 - (0/4) * Real.log 4 by simp]
          apply Tendsto.sub
          · -- The x * log(x) term tends to 0 as x → 0⁺
            apply Tendsto.mul
            · exact tendsto_const_nhds
            · -- change of variable: The u= log(x): x *log x= u * exp u
              let f := fun x ↦ - ((- Real.log x) * Real.exp (Real.log x))
              refine (tendsto_congr' (f₂ := f) ?_).mpr ?_
              · filter_upwards [self_mem_nhdsWithin] with x hx; simp [f]
                have hx0 : 0 < x := by simpa using hx
                rw [mul_comm, Real.exp_log hx0 ]
              · -- Using the growth comparison: u * exp(u) → 0 as u → -∞
                unfold f
                ring_nf
                have h_ueu : Tendsto (fun u ↦ u * rexp u) atBot (𝓝 0) := by
                  simpa [Function.comp_def] using (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).neg.comp tendsto_neg_atBot_atTop
                simpa [Function.comp_def] using h_ueu.comp Real.tendsto_log_nhdsGT_zero
          · -- The (x/4) * log(4 + x²) term tends to 0 as x → 0
            apply Tendsto.mul
            · ring_nf ; simpa using (continuous_id.mul (continuous_const (y := (4 : ℝ)⁻¹))).tendsto 0 |>.mono_left nhdsWithin_le_nhds
            · ring_nf
              have h_cont : Continuous (fun x : ℝ ↦ Real.log (4 + x^2)) := (continuous_const.add (continuous_id.pow 2)).log (fun x ↦ by nlinarith)
              simpa using (h_cont.tendsto 0).mono_left nhdsWithin_le_nhds
      · -- Limit of arctan(2/x) as x → 0⁺ is π/2
        -- Since 2/x → +∞, arctan(2/x) → π/2
        have h_div : Tendsto (fun x : ℝ ↦ 2 / x) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
        simpa [Function.comp_def] using (tendsto_arctan_atTop.comp h_div).mono_right nhdsWithin_le_nhds

  -- Step 3: By uniqueness of limits, the integral equals π/2
  exact tendsto_nhds_unique h_lim_int h_lim_int2

lemma h_lim_T: Tendsto (fun T ↦ (sinc (T / 2))^2 * (T / 2)) (atTop : Filter ℝ) (𝓝 0) := by
  have h_inner : Tendsto (fun T : ℝ ↦ T / 2) atTop atTop := tendsto_id.atTop_mul_const (by norm_num : (0 : ℝ) < 2⁻¹)
  simpa [Function.comp_def] using limit_sinc_sq_mul_self_atTop.comp h_inner

theorem integral_dirichlet : Tendsto (fun T ↦ ∫ t in 0..T, sinc t) atTop (𝓝 (π / 2)) := by
  -- Step 1: Replace the integral of sinc with the identity involving the integral of sinc²
  -- We use the identity: ∫₀ᵀ sinc(t) dt = ∫₀ᵀ/² sinc²(t) dt + sinc(T/2)² * (T/2)
  refine Tendsto.congr' (f₁ := fun T:ℝ ↦ (∫ t in 0..T/2, (Real.sinc t)^2) + (Real.sinc (T/2))^2 * (T/2)) ?_ ?_
  · -- This identity holds for all T > 0
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [integral_sinc_zero_T T hT]
  · -- Step 2: Evaluate the limit as T → ∞
    -- The target value is π/2 + 0
    rw [← add_zero (π / 2), ← integral_sinc_sq_eq_pi_div_two]
    -- 1. The integral part: ∫₀ᵀ/² sinc²(t) dt converges to the improper integral over Ioi 0
    -- as T/2 → ∞.
    exact (MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 integrable_sinc_sq
      (tendsto_id.atTop_mul_const (by norm_num))).add h_lim_T

lemma HeavisideNorm_le_one : ∀ a:ℝ, ‖HeavisidePerso  a‖ ≤ 1 := by
  unfold HeavisidePerso
  intro a
  split_ifs with h1 h2
  ·simp
  ·norm_num
  ·norm_num

theorem lim_S_Rx (x : ℝ) : Tendsto (fun R ↦ DirichletSin (R * x)) atTop (𝓝 (HeavisidePerso x)) := by
  unfold DirichletSin HeavisidePerso
  -- Split into three cases for x: x < 0, x = 0, and x > 0
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [hx, hx.ne, not_lt_of_lt hx]
    -- it suffices that the integral part tends to -π/2
    suffices Tendsto (fun R ↦ ∫ t in 0..R*x, sinc t) atTop (𝓝 (-π/2)) by
      convert (this.const_mul (1/π)).const_add (1/2) using 2
      ·field_simp
      · field_simp
        ring_nf

    -- Since x < 0 and R → ∞, the upper bound R*x → -∞.
    -- We use the change of variable t ↦ -t to transform this into the standard Dirichlet integral.
    have h_lim_pos : Tendsto (fun R ↦ - (R * x)) atTop atTop := tendsto_neg_atBot_atTop.comp (tendsto_id.atTop_mul_const_of_neg hx)
    convert (integral_dirichlet.comp h_lim_pos).neg using 1
    · ext R
      dsimp only [Function.comp_apply, neg_mul_eq_mul_neg]
      -- Use the property that sinc is an even function: sinc(-t) = sinc(t)
      rw [← neg_neg (R * x),show (0 : ℝ) = -0 by simp, ← intervalIntegral.integral_comp_neg (fun t ↦ sinc t), neg_zero]
      simp only [sinc_neg]
      rw [intervalIntegral.integral_symm, neg_neg (R * x)]
    · ring_nf
  · -- Case x = 0: DirichletSin(0) is defined as 1/2
    simp
  · -- Case x > 0: The limit is 1
    simp [hx]
    -- it suffices that the integral part tends to -π/2
    suffices Tendsto (fun R ↦ ∫ t in 0..R*x, sinc t) atTop (𝓝 (π/2)) by
      convert (this.const_mul (1/π)).const_add (1/2) using 2
      ·field_simp
      · field_simp
        ring_nf
    -- Since x > 0, R*x → ∞, so we simply compose the previously proven integral_dirichlet
    convert integral_dirichlet.comp (tendsto_id.atTop_mul_const hx) using 2

lemma DirichletSin_continuous : Continuous fun u ↦ DirichletSin (u):= by
  unfold DirichletSin
  apply Continuous.add
  · continuity
  · apply Continuous.mul
    · continuity
    · apply intervalIntegral.continuous_primitive
      apply Continuous.intervalIntegrable
      exact continuous_sinc

lemma DirichletSin_continuous_comp (T:ℝ)(t:ℝ):Continuous fun x ↦ (DirichletSin (T * (x - t))):= by
  unfold DirichletSin
  push_cast
  apply Continuous.add
  · continuity
  · apply Continuous.mul
    · continuity
    · have : Continuous (fun x ↦ (∫ (t : ℝ) in 0..T * (x - ↑t), sinc t)):= by
        let F := fun (u : ℝ) ↦ ∫ (s : ℝ) in (0)..u, sinc s
        let g := fun (x : ℝ) ↦ T * (x - t)
        change Continuous (F ∘ g)
        apply Continuous.comp
        apply intervalIntegral.continuous_primitive
        apply Continuous.intervalIntegrable
        exact continuous_sinc
        unfold g
        apply Continuous.mul
        apply continuous_const
        apply Continuous.sub
        apply continuous_id
        apply continuous_const
      exact this

theorem DirichletSinBounded:  ∃ M, ∀ y, |DirichletSin y| ≤ M := by
  -- Step 1: Prove the function converges to 1 at +∞
  have h_lim_top : Tendsto DirichletSin atTop (𝓝 1) := by
    convert integral_dirichlet.const_mul (1/π) |>.const_add (1/2) using 1
    field_simp [Real.pi_ne_zero]; ring

  -- Step 2: Prove the function converges to 0 at -∞
  have h_lim_bot : Tendsto DirichletSin atBot (𝓝 0) := by
    let f_sym := fun u ↦ 1/2 + 1/π * (- ∫ t in 0..-u, sinc t)
    refine Tendsto.congr' (f₁ := f_sym) ?_ ?_
    · filter_upwards with u
      unfold DirichletSin f_sym
      rw [show (0 : ℝ) = -0 by simp, ← intervalIntegral.integral_comp_neg Real.sinc, show (-0 : ℝ) = 0 by simp]
      simp only [Real.sinc_neg, neg_zero]
      rw [intervalIntegral.integral_symm]
      ring_nf
    · convert (integral_dirichlet.comp tendsto_neg_atBot_atTop).neg.const_mul _ |>.const_add _ using 1
      field_simp [Real.pi_ne_zero]; ring

  -- Step 3: Use the limits to find bounds outside a large interval [-R, R]
    -- Since the limit at +∞ is 1, the function stays near 1 (and thus < 2) for large positive y
  have h_evt_top : ∀ᶠ y in atTop, ‖DirichletSin y‖ < 2 :=
    (h_lim_top.norm).eventually (eventually_lt_nhds (show ‖(1:ℝ)‖ < 2 by norm_num))
  obtain ⟨R_top, h_top⟩ := Filter.mem_atTop_sets.mp h_evt_top

  -- Since the limit at -∞ is 0, the function stays near 0 (and thus < 2) for large negative y
  have h_evt_bot : ∀ᶠ y in atBot, ‖DirichletSin y‖ < 2 :=
    (h_lim_bot.norm).eventually (eventually_lt_nhds (show ‖(0:ℝ)‖ < 2 by norm_num))
  obtain ⟨R_bot, h_bot⟩ := Filter.mem_atBot_sets.mp h_evt_bot

  -- Step 4: Bound the function on the central compact interval [-R, R]
  let R := max |R_top| |R_bot|
  -- A continuous function on a compact set is bounded (Extreme Value Theorem)
  obtain ⟨B, hB⟩ := (isCompact_Icc.image DirichletSin_continuous).isBounded.exists_norm_le

  -- Step 5: Combine the local bound (B) and the tail bound (2)
  use max B 2
  intro y
  rw [← Real.norm_eq_abs]
  by_cases hy : |y| ≤ R
  · -- Case |y| ≤ R: use the bound from the compact interval
    rw [abs_le] at hy
    exact le_trans (hB _ (mem_image_of_mem _ hy)) (le_max_left _ _)
  · -- Case |y| > R: use the bound from the limits at infinity
    rw [ not_le,lt_abs] at hy
    apply le_trans _ (le_max_right B 2)
    cases hy with
    | inl hy_pos =>
      have : y ≥ R_top := by
        apply le_trans _ (le_of_lt hy_pos)
        trans |R_top|; exact le_abs_self _; exact le_max_left _ _
      exact le_of_lt (h_top y this)
    | inr hy_neg =>
      have : y ≤ R_bot := by
        have hy_rev : y < -R := by linarith [hy_neg]
        apply le_trans (le_of_lt hy_rev)
        trans -|R_bot|; simp; exact le_max_right _ _; exact neg_abs_le R_bot
      exact le_of_lt (h_bot y this)

theorem DirichletSinBoundedComp (T t : ℝ) (hT : T ≥ 0) : ∃ C : ℝ, ∀ x, |DirichletSin (T * (x - t))| ≤ C := by
  obtain ⟨M, hM⟩ := DirichletSinBounded
  use M
  intro x
  exact hM (T * (x - t))

lemma DirichletSinBoundedComp_forall (t : ℝ) :
    ∃ C : ℝ, ∀ T , ∀ x : ℝ, |DirichletSin (T * (x - t))| ≤ C := by --uniform with respect to T and t
  -- Use the previously proven global bound for DirichletSin
  obtain ⟨C, hC⟩ := DirichletSinBounded
  -- The bound C works for any input, including the composition T * (x - t)
  exact ⟨C, fun T x => hC (T * (x - t))⟩

theorem Integrable_DirichletSin_times_integrableFunction (f:ℝ → ℝ ) (T t: ℝ ) (hT: T≥ 0) (hf: Integrable (fun t ↦ f t )): Integrable (fun x => f x * DirichletSin (T * (x - t))):= by
  obtain ⟨C, hC⟩ := DirichletSinBoundedComp T t hT
  have g_AESM: AEStronglyMeasurable (fun x ↦ DirichletSin (T * (x - t))) volume:= by
    apply Continuous.aestronglyMeasurable
    exact DirichletSin_continuous_comp T t
  have h_g_filter_bounded : ∀ᵐ (x : ℝ), ‖DirichletSin (T * (x - t))‖ ≤ C:= by
    filter_upwards
    simp_rw [Real.norm_eq_abs]
    exact hC
  apply MeasureTheory.Integrable.mul_bdd (f:= f) (g:=fun x => DirichletSin (T * (x - t)) ) (c:= C) hf g_AESM h_g_filter_bounded

theorem Integrable_DirichletSin_times_integrableFunction' (f:ℝ → ℂ ) (T t: ℝ ) (hT: T≥ 0) (hf: Integrable (fun t ↦ f t )): Integrable (fun x => f x * ↑(DirichletSin (T * (x - t)))):= by
  obtain ⟨C, hC⟩ := DirichletSinBoundedComp T t hT
  have g_AESM: AEStronglyMeasurable (fun x ↦ (↑(DirichletSin (T * (x - t))) : ℂ)) volume:= by
    apply Continuous.aestronglyMeasurable
    have h_cont_re:=  (DirichletSin_continuous_comp T t)
    exact continuous_ofReal.comp h_cont_re
  have h_g_filter_bounded : ∀ᵐ (x : ℝ), ‖(↑(DirichletSin (T * (x - t))) : ℂ)‖ ≤ C:= by
    filter_upwards
    simp_rw[Complex.norm_real]
    simp_rw [Real.norm_eq_abs]
    exact hC
  apply MeasureTheory.Integrable.mul_bdd (f:= f) (g:=fun x => DirichletSin (T * (x - t)) ) (c:= C) hf g_AESM h_g_filter_bounded

theorem Tendsto_Integral_DirichletSin_times_integrableFunction (f : ℝ → ℝ) (t : ℝ) (hf : Integrable (fun t ↦ f t)) :
    Tendsto (fun T : ℝ ↦ ∫ a, f a * DirichletSin (T * (a - t)))
    atTop (𝓝 (∫ a in Ioi t, f a)) := by
  -- Step 1: Obtain a uniform bound C for the DirichletSin function
  rcases DirichletSinBoundedComp_forall t with ⟨C, hC⟩
  -- Rewrite the limit integral using an indicator function for the interval (t, ∞)
  rw [← integral_indicator measurableSet_Ioi]

  -- Step 2: Apply the Dominated Convergence Theorem (DCT)
  -- The dominating function is |f(a)| * |C|, which is integrable since f is integrable.
  apply tendsto_integral_filter_of_dominated_convergence (fun a ↦ |f a| * |C|)
  · -- Prove measurability of the integrand for sufficiently large T
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact (Integrable_DirichletSin_times_integrableFunction f T t hT hf).aestronglyMeasurable
  · -- Prove the domination condition: |f(a) * DirichletSin(T(a-t))| ≤ |f(a)| * |C|
    apply Filter.Eventually.of_forall
    intro T
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left ((hC T x).trans (le_abs_self C)) (abs_nonneg _)
  · -- Verify the integrability of the dominating function
    exact hf.abs.mul_const _
  · -- Step 4: Handle the pointwise convergence almost everywhere
    -- We exclude the single point a = t, which has measure zero.
    have h_neq : ∀ᵐ a, a ≠ t := by
      rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton];  exact measure_singleton t
    filter_upwards [h_neq] with a ha
    rw [Set.indicator_apply]
    -- Use the pointwise limit of DirichletSin, which is the HeavisidePerso function
    have h_lim : Tendsto (fun T ↦ DirichletSin (T * (a - t))) atTop (𝓝 (HeavisidePerso (a - t))) := lim_S_Rx (a - t)
    split_ifs with h_io
    · -- Case a > t: HeavisidePerso(a - t) = 1
      rw [HeavisidePerso, if_pos (sub_pos.mpr h_io)] at h_lim
      apply Tendsto.const_mul (f a) at h_lim
      rw [mul_one] at h_lim ; exact h_lim
    · -- Case a < t (since a ≠ t): HeavisidePerso(a - t) = 0
      simp only [mem_Ioi, not_lt] at h_io
      have ha_lt : a < t := lt_of_le_of_ne h_io ha
      have h_neg : a - t < 0 := sub_neg.mpr ha_lt
      rw [HeavisidePerso, if_neg h_neg.not_lt, if_neg h_neg.ne] at h_lim
      apply Tendsto.const_mul (f a) at h_lim
      rw [mul_zero] at h_lim; exact h_lim

--same theorem but this time with a complex-valued function f:ℝ → ℂ
theorem Tendsto_Integral_DirichletSin_times_integrableFunction' (f:ℝ → ℂ ) (t: ℝ ) (hf: Integrable (fun t ↦ f t )):
 Tendsto (fun T : ℝ ↦ ∫ a, f a * ↑(DirichletSin (T * (a - t))))
    atTop (𝓝 (∫ a in Ioi t, f a)):= by
  rcases DirichletSinBoundedComp_forall t with ⟨C, hC⟩
  rw [← integral_indicator measurableSet_Ioi]
  apply tendsto_integral_filter_of_dominated_convergence (fun a ↦ ‖f a‖* |C|)
  · filter_upwards [eventually_ge_atTop 0] with T hT
    exact (Integrable_DirichletSin_times_integrableFunction' f T t hT hf).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro T
    apply Filter.Eventually.of_forall
    intro x
    rw [ norm_mul, Complex.norm_real]
    apply mul_le_mul_of_nonneg_left
    · exact (hC T x).trans (le_abs_self C)
    · exact norm_nonneg (f x)
  · exact hf.norm.mul_const |C|
  · have h_neq : ∀ᵐ a, a ≠ t := by
      rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton];  exact measure_singleton t
    filter_upwards [h_neq] with a ha
    rw [Set.indicator_apply]
    have h_lim : Tendsto (fun T ↦ DirichletSin (T * (a - t))) atTop (𝓝 (HeavisidePerso (a - t))) := lim_S_Rx (a - t)
    split_ifs with h_io
    · rw [HeavisidePerso, if_pos (sub_pos.mpr h_io)] at h_lim
      have h_lim_2 : Tendsto (fun T ↦ (DirichletSin (T * (a - t)) : ℂ)) atTop (𝓝 (1 : ℂ)) :=by simpa using h_lim.ofReal
      apply Tendsto.const_mul (f a) at h_lim_2
      rw [mul_one] at h_lim_2 ; exact h_lim_2
    · simp only [mem_Ioi, not_lt] at h_io
      have ha_lt : a < t := lt_of_le_of_ne h_io ha
      have h_neg : a - t < 0 := sub_neg.mpr ha_lt
      rw [HeavisidePerso, if_neg h_neg.not_lt, if_neg h_neg.ne] at h_lim
      have h_lim_2 : Tendsto (fun T ↦ (DirichletSin (T * (a - t)) : ℂ)) atTop (𝓝 (0 : ℂ)) :=by simpa using h_lim.ofReal
      apply Tendsto.const_mul (f a) at h_lim_2
      rw [mul_zero] at h_lim_2; exact h_lim_2

--this time the integral is restricted to (0, ∞)
theorem Tendsto_Integral_DirichletSin_times_integrableFunction_zero' (f : ℝ → ℂ) (t : ℝ) (hf : Integrable (fun t ↦ f t)) :
    Tendsto (fun T : ℝ ↦ ∫ a in Ioi 0, f a * ↑(DirichletSin (T * (a - t))))
      atTop (𝓝 (∫ a in Ioi (max 0 t), f a)) := by
  have h_ae_neq : ∀ᵐ a, a ≠ t := by
    rw [ae_iff]
    have : {a | ¬a ≠ t} = {t} := by ext a ; simp
    rw [this]
    exact volume_singleton (a:=t)
  rcases DirichletSinBoundedComp_forall t with ⟨C, hC⟩
  convert tendsto_integral_filter_of_dominated_convergence (fun a ↦ ‖f a‖ * |C|) (f := fun a ↦ f a * ↑(HeavisidePerso (a - t))) (l := atTop) ?_ ?_ ?_ ?_ using 1
  · congr 1
    symm
    rw [← integral_indicator measurableSet_Ioi]
    conv_rhs => rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    unfold HeavisidePerso
    filter_upwards [h_ae_neq] with a hat
    by_cases ha0 : a ∈ Ioi 0
    · rw [indicator_of_mem ha0]
      simp only [mem_Ioi] at ha0
      split_ifs with h_pos h_zero
      · simp only [sub_pos] at h_pos
        rw [indicator_of_mem];simp
        rwa [mem_Ioi, max_lt_iff, and_iff_right ha0]
      · exfalso
        exact hat (sub_eq_zero.mp h_zero)
      · rw [indicator_of_not_mem]; push_cast; rw[mul_zero]
        rw [mem_Ioi, max_lt_iff, not_and_or, not_lt]; right ;linarith
    · rw [indicator_of_not_mem ha0, indicator_of_not_mem]
      rw [mem_Ioi, not_lt]
      rw[mem_Ioi] at ha0
      have h_ale0 : a ≤ 0 := by linarith [ha0]
      exact h_ale0.trans (le_max_left 0 t)
  · exact instIsCountablyGenerated_atTop
  · filter_upwards [eventually_ge_atTop 0] with T hT
    exact (Integrable_DirichletSin_times_integrableFunction' f T t hT hf).aestronglyMeasurable.restrict
  · filter_upwards with a
    filter_upwards with x
    rw [norm_mul]; rw [Complex.norm_real]
    refine mul_le_mul_of_nonneg_left ((hC _ _).trans (le_abs_self C)) (norm_nonneg _)
  · exact hf.norm.mul_const |C| |>.restrict
  · filter_upwards with a
    apply Tendsto.const_mul
    simpa using (lim_S_Rx (a - t)).ofReal
