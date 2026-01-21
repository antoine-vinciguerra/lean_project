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

import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.FourierTransform

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Commute.Defs
import LaplaceTransform.LaplaceTransformDef
import LaplaceTransform.DirichletIntegral
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.Analysis.Complex.Exponential

import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
/-!


# The Real Version of the Laplace transform

-/

@[expose] public section


noncomputable section


open MeasureTheory Filter
open MeasureTheory Set
open MeasureTheory Complex Real Topology Filter
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

def μ_T: ℝ → Measure ℝ := fun T ↦ volume.restrict (Icc (-T) T)


-- Now define the same for the right hand halfplane of the complex

def RealFullLaplaceKernel (f :ℝ → ℂ) (p : ℂ) : realLine→ ℂ :=
  let g (x : realLine): ℂ:= f (realLine_to_real x)
  fun x ↦(fullLaplaceKernel realLine L g p) x


def RealLaplaceTransform (f :ℝ  → ℂ) : ℂ → ℂ  :=
  let g (x : realLine): ℂ:= f (realLine_to_real x)
  GeneralizedLaplaceTransform realLine L g μ_r

theorem RealLaplaceTransform_const_smul
   (f :ℝ → ℂ)  (r p : ℂ)
   (h_int : Integrable (RealFullLaplaceKernel f p ) μ_r) :
  RealLaplaceTransform  (r • f) p = r • RealLaplaceTransform f p := by
  unfold RealLaplaceTransform
  let g (x : realLine): ℂ:= f (realLine_to_real x)
  apply GeneralizedLaplaceTransform_const_smul realLine L g μ_r r p h_int
  apply (inferInstance : CompleteSpace ℂ)
  apply (inferInstance : IsBoundedSMul ℂ ℂ)

theorem RealLaplaceTransform_additive
   (f₁ : ℝ → ℂ)(f₂: ℝ → ℂ) (p : ℂ)
  (h_int₁ : Integrable (RealFullLaplaceKernel f₁ p) μ_r)
  (h_int₂ : Integrable (RealFullLaplaceKernel f₂ p) μ_r):
  RealLaplaceTransform (f₁ + f₂) p =  RealLaplaceTransform f₁ p + RealLaplaceTransform f₂ p := by
  let g₁ (x : realLine): ℂ:= f₁ (realLine_to_real x)
  let g₂ (x : realLine): ℂ:= f₂ (realLine_to_real x)
  unfold RealLaplaceTransform
  apply GeneralizedLaplaceTransform_additive realLine L g₁ g₂ μ_r p h_int₁ h_int₂

theorem RealLaplaceTransformIs (f: ℝ → ℂ) (hf : Measurable f) (p: ℂ):
RealLaplaceTransform f p = ∫t,cexp (-p*t) * (f t) ∂μ_real  := by
  change (GeneralizedLaplaceTransform realLine L (fun x => f (realLine_to_real x)) μ_r) p =
         ∫ t, cexp (-p * t) * f t ∂μ_real
  simp [GeneralizedLaplaceTransform]
  unfold fullLaplaceKernel
  unfold laplaceKernel
  have hL_x_realLine: ∀ x : realLine, NormedSpace.exp ℂ (-L x p) = NormedSpace.exp ℂ (-x.val * p) := by
    intro x; simp [L]

  have h_unfold_g : ∀ e : realLine, (fun x ↦ f (realLine_to_real x)) e = f (realLine_to_real e):= by
    simp only [implies_true]
  have exp_eq : ∀ z : ℂ, (NormedSpace.exp ℂ z) = Complex.exp z := by
    intro z
    rw [Complex.exp_eq_exp_ℂ]

  calc  ∫ (e : ↑realLine), (fun x ↦ f (realLine_to_real x)) e * NormedSpace.exp ℂ (-L e p) • 1 ∂μ_r
    _=∫ (e : ↑realLine),  f (realLine_to_real e)* NormedSpace.exp ℂ (-L e p) • 1 ∂μ_r:= by
      congr
    _ =∫ (e : ↑realLine),  f (realLine_to_real e)* NormedSpace.exp ℂ (-e.val * p) • 1 ∂μ_r:= by
      congr
      ext e
      rw[hL_x_realLine]
    _=∫ (e : ↑realLine),  f (realLine_to_real e)* Complex.exp (-e.val * p)  • 1 ∂μ_r:= by
      congr
      ext e
      rw[exp_eq]
    _=∫ (t : ℝ), (f (realLine_to_real (real_to_realLine t))) * Complex.exp (- (real_to_realLine t).val * p) • (1 : ℂ) ∂μ_real := by
      have h_μ: μ_r = Measure.map real_to_realLine μ_real := rfl
      rw[h_μ]
      have real_to_realLine_measurable : Measurable real_to_realLine := by
        apply Measurable.subtype_mk
        exact measurable_ofReal

      have realLine_to_real_measurable : Measurable realLine_to_real := by
        have val_measurable : Measurable (Subtype.val : realLine → ℂ) :=
        measurable_subtype_coe
        have re_measurable : Measurable Complex.re := measurable_re
        exact re_measurable.comp val_measurable

      have h_meas_g : Measurable (fun e : realLine =>
  f (realLine_to_real e) * Complex.exp (- e.val * p)• (1 : ℂ)) := by
        have g1 : Measurable (fun e : realLine => f (realLine_to_real e)) := Measurable.comp hf realLine_to_real_measurable
        have g2 : Measurable (fun e : realLine => Complex.exp (- e.val * p)) := by
          have measure_exp : Measurable (Complex.exp) :=
            continuous_exp.measurable
          have measure_exponent : Measurable (fun e : realLine => - (e.val * p)) :=
            (continuous_neg.comp (continuous_mul_right p)).measurable.comp measurable_subtype_coe
          have two_funct_eq: (fun e : realLine => - (e.val * p))= (fun e : realLine => - e.val * p) :=by
            funext e
            simp only [neg_mul]
          rw[two_funct_eq] at measure_exponent
          exact measure_exp.comp (measure_exponent)
        have g1_mul_g2: Measurable (fun e : realLine =>
        f (realLine_to_real e) * Complex.exp (- e.val * p)):= g1.mul g2
        have two_funct_eq_bis: (fun e : realLine =>
        f (realLine_to_real e) * Complex.exp (- e.val * p))=
        (fun e : realLine =>
        f (realLine_to_real e) * Complex.exp (- e.val * p)• (1 : ℂ)) :=by
          funext e
          simp_all only [neg_mul, Subtype.forall, implies_true, smul_eq_mul, mul_one]
        rw[two_funct_eq_bis] at g1_mul_g2
        exact g1_mul_g2

      have h_aemeas_map : AEMeasurable real_to_realLine μ_real := real_to_realLine_measurable.aemeasurable
      have h_aestrongly_meas_g : AEStronglyMeasurable (fun e : ↑realLine => f (realLine_to_real e) * Complex.exp (-e.val * p)• (1 : ℂ)) μ_r :=
        h_meas_g.aestronglyMeasurable

      rw [MeasureTheory.integral_map h_aemeas_map h_aestrongly_meas_g]
    _= ∫ (t : ℝ), f (t) * Complex.exp (- (real_to_realLine t).val * p) • (1 : ℂ) ∂μ_real := by
      congr
    _=∫ (t : ℝ), f (t) * Complex.exp (- t * p) • (1 : ℂ) ∂μ_real :=  by
      congr
    _= ∫ (t : ℝ), f (t) * Complex.exp (- t * p) ∂μ_real := by
      congr
      funext e
      simp_all only [neg_mul, Subtype.forall, implies_true, smul_eq_mul, mul_one]
    _= ∫ (t : ℝ), f (t) * Complex.exp (- (t * p)) ∂μ_real := by
      congr
      funext x
      rw [@neg_mul]
    _=∫ (t : ℝ), f (t) * Complex.exp (- (p*t)) ∂μ_real := by
      congr
      funext x
      rw [← mul_comm p x]
    _=∫ (t : ℝ), Complex.exp (- (p*t))* f (t)  ∂μ_real := by
      congr
      funext x
      rw [← mul_comm]


end Defs

section LaplaceInverse
--In this section we will prove the formula of the inverse Fourier Transform
-- First we need to define what will be in the integrand
--the integral sum is defined over the sum of two reals

lemma integral_cexp_Icc_Dirichlet
    {T t a : ℝ}
    {hT : 0 ≤ T} :
    (∫ r in Icc (-T) T, cexp (I * (r:ℂ) * (t - a)))
      =
    if h : t - a = 0
    then (2 * T : ℂ)
    else 2 * Real.sin (T * (t - a)) / (t - a) := by
  classical
  set ω : ℝ := t - a
  by_cases hω : ω = 0
  · simp [ω, hω]
    have hta : t-a = 0:= by simpa [ω] using hω
    have htaC : ((t : ℂ) - a = 0) := by
      simpa using congrArg (fun x : ℝ => (x : ℂ)) hta
    calc ∫ (r : ℝ) in Icc (-T) T, cexp (I * ↑r * (↑t - ↑a))
    _= ∫ (r : ℝ) in Icc (-T) T, cexp (I * ↑r * (0)):= by
      congr
      ext r
      rw[htaC]
    _=∫ (r : ℝ) in Icc (-T) T, cexp (0):= by
      congr
      ext r
      simp
    _=∫ (r : ℝ) in Icc (-T) T, 1:= by
      congr
      ext r
      simp
    _= 2*T := by
      rw [@setIntegral_const]
      simp only [volume_real_Icc, sub_neg_eq_add, real_smul, mul_one]
      simp [ hT]
      rw [@two_mul]
  · simp [hω, ω]
    have: ∫ (r : ℝ) in Icc (-T) T, cexp (I * ↑r * (↑t - ↑a))= ∫ (r : ℝ) in -T..T, cexp (I * ↑r * (↑t - ↑a)):= by
      rw [@integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le]
      simp[hT]
    rw[this]
    have: ∫ (r : ℝ) in -T..T, cexp (I * ↑r * (↑t - ↑a))= ∫ (r : ℝ) in -T..T, cexp (I * (ω:ℂ)* ↑r) := by
      congr
      ext r
      have : ↑t - ↑a= (ω:ℂ) := by
        rw [ofReal_sub]
      rw[this]
      ring_nf
    rw[this]
    rw[integral_exp_mul_complex]
    case neg=>
      have : cexp (I * ↑ω * ↑(-T))= cexp (-I *  (↑T* ↑ω)):= by
            push_cast
            ring_nf
      rw[this]
      have : cexp (I * ↑ω * T)= cexp (I *  (↑T* ↑ω)):= by
            ring_nf
      rw[this]
      have : cexp (I * (↑T * ↑ω)) - cexp (-I * (↑T * ↑ω))= 2* I * Complex.sin (↑T * ↑ω) := by
        unfold Complex.sin
        ring_nf
        simp[I_sq]
        ring_nf
      rw[this]
      unfold ω
      simp only [ofReal_sub]
      have hI : I ≠ 0 := I_ne_zero
      have h_wa : ((t : ℂ) - a) ≠ 0 := by
        simp [ω] at hω
        rw[← ofReal_sub]
        exact ofReal_ne_zero.mpr hω

      field_simp [hI, h_wa]
    case neg=>
      apply mul_ne_zero
      · exact I_ne_zero
      · exact ofReal_ne_zero.mpr hω




def imNbFromReals (γ : ℝ) (T : ℝ) : ℂ :=
  (γ : ℂ) + (T : ℂ) * I
def InverseLaplaceKernel (F : ℂ → ℂ) (t : ℝ) : ℝ → ℝ → ℂ :=
  fun γ T ↦ I*(Complex.exp ( (imNbFromReals γ T) * t)) * F (imNbFromReals γ T)

def InverseLaplaceKernelFunctT (F : ℂ → ℂ) (t : ℝ)(γ : ℝ): ℝ→ ℂ:=
  (InverseLaplaceKernel F t) γ

theorem InverseLaplaceKernelAdditive (F₁ : ℂ → ℂ) (F₂ : ℂ → ℂ)(t : ℝ):
  InverseLaplaceKernel (F₁+F₂) t = (InverseLaplaceKernel F₁ t) +(InverseLaplaceKernel F₂ t):=by
    funext γ
    funext T
    unfold InverseLaplaceKernel

    calc I * cexp (imNbFromReals γ T * ↑t) * (F₁ + F₂) (imNbFromReals γ T)
      _= I * cexp (imNbFromReals γ T * ↑t) *(F₁ (imNbFromReals γ T) + F₂ (imNbFromReals γ T)):= by
        simp_all only [Pi.add_apply]
      _=I * cexp (imNbFromReals γ T * ↑t) *F₁ (imNbFromReals γ T) + I * cexp (imNbFromReals γ T * ↑t) *F₂ (imNbFromReals γ T) := by
        rw [@left_distrib]

theorem InverseLaplaceKernelConst (F : ℂ → ℂ)(c:ℂ)(t : ℝ):
  InverseLaplaceKernel (c •F) t = c •(InverseLaplaceKernel F t):=by
    funext γ
    funext T
    unfold InverseLaplaceKernel

    calc I * cexp (imNbFromReals γ T * ↑t) * (c • F) (imNbFromReals γ T)
      _= I * cexp (imNbFromReals γ T * ↑t) * c * F (imNbFromReals γ T):= by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← @NonUnitalRing.mul_assoc]
      _= I * c* cexp (imNbFromReals γ T * ↑t) * F (imNbFromReals γ T):= by
        rw [@mul_mul_mul_comm']
      _= c*I *cexp (imNbFromReals γ T * ↑t) * F (imNbFromReals γ T):= by
        ring
      _= (c • fun γ T ↦ I * cexp (imNbFromReals γ T * ↑t) * F (imNbFromReals γ T)) γ T:= by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring


--We know define the inverseLaplace. This is conditioned to gamma being chosen so that our integral is integrable
def inverseLaplace_t (F : ℂ → ℂ) (γ t : ℝ)
 : ℂ :=
  1/(2*I*Real.pi ) * ∫ T : ℝ, InverseLaplaceKernel F t γ T

def inverseLaplace_tBounded (F : ℂ → ℂ) (γ T t: ℝ)
 : ℂ :=
  1/(2*I*Real.pi ) * ∫ r in Icc (-T) T , InverseLaplaceKernel F t γ r


def inverseLaplaceFunction (F : ℂ → ℂ) (γ: ℝ) (S: Set ℝ)
(h_integrable_in_S : ∀ t∈ S, Integrable ((InverseLaplaceKernelFunctT F t) γ ) volume)
 : S → ℂ :=
fun t↦ inverseLaplace_t F γ t

def inverseLaplaceFunctionBounded (F : ℂ → ℂ) (γ T: ℝ) (S: Set ℝ)
(h_integrable_in_S : ∀ t∈ S, Integrable ((InverseLaplaceKernelFunctT F t) γ ) volume)
 : S → ℂ :=
 fun t↦ inverseLaplace_tBounded F γ T t


theorem limit_inverseLaplace_bounded_eq_full
  (F : ℂ → ℂ) (γ : ℝ) (S : Set ℝ)
  (t : S)
  {h_integrable_in_S : ∀ t∈ S, Integrable ((InverseLaplaceKernelFunctT F t) γ ) volume}
  :
  Tendsto (fun T ↦ inverseLaplaceFunctionBounded F γ T S h_integrable_in_S t) atTop (nhds (inverseLaplaceFunction F γ S h_integrable_in_S t)) := by
    unfold inverseLaplaceFunction
    unfold inverseLaplaceFunctionBounded
    unfold inverseLaplace_t
    unfold inverseLaplace_tBounded

    apply Tendsto.const_mul

  -- We want to prove  ∫_{-T}^{T} f -> ∫_{-∞}^{+∞} f

    let f := fun x ↦ InverseLaplaceKernel F t γ x


  --We are changing the integral over an interval to the integral over R with an indicator
    have eq_indicator : ∀ T, ∫ r in Icc (-T) T, f r = ∫ r, (Icc (-T) T).indicator f r := by
      intro T
      rw [integral_indicator (measurableSet_Icc : MeasurableSet (Icc (-T) T))]

    change Tendsto (fun k ↦ ∫ r in Icc (-k) k, f r) atTop (nhds (∫ x, f x))

    simp_rw[eq_indicator]
    apply tendsto_integral_filter_of_dominated_convergence (fun a ↦ ‖f a‖)

    -- First goal: prove Measurability
    · have hf : AEStronglyMeasurable f volume := (h_integrable_in_S t t.2).aestronglyMeasurable
      have hf_indicator: ∀ (T : ℝ), AEStronglyMeasurable ((Icc (-T) T).indicator f) volume:= by
        intro T
        apply AEStronglyMeasurable.indicator
        · exact hf
        · exact measurableSet_Icc
      simp[hf_indicator]
    -- Second goal: prove Domination
    · have hf_norm: ∀ (T a : ℝ), ‖(Icc (-T) T).indicator f a‖ ≤ ‖f a‖:= by
        intro T a
        by_cases ha_in : a ∈ Icc (-T) T
        · rw [Set.indicator_of_mem ha_in]
        · rw [Set.indicator_of_notMem ha_in]
          simp[norm_zero]
      simp[hf_norm]
    -- Third goal: prove Integrability
    · have h_integrable : Integrable f volume := h_integrable_in_S t t.2
      exact h_integrable.norm
    -- Fourth goal: prove Limit
    · apply ae_of_all
      intro a
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.Ici_mem_atTop ‖a‖]
      intro n hn
      have h_le : ‖a‖ ≤ n := by exact mem_Ici.mp hn
      have ha_in : a ∈ Icc (-n) n := by
        rw [mem_Icc]
        constructor
        · linarith [abs_le.mp h_le]
        · linarith [abs_le.mp h_le]
      exact (Set.indicator_of_mem ha_in f).symm


theorem inverseLaplaceAdditive_t(F₁: ℂ → ℂ) (F₂: ℂ → ℂ)(γ t : ℝ)
(h₁ :  Integrable (InverseLaplaceKernelFunctT F₁ t γ ) volume)
(h₂ : Integrable (InverseLaplaceKernelFunctT F₂ t γ ) volume):
inverseLaplace_t (F₁+F₂) γ t = inverseLaplace_t F₁ γ t + inverseLaplace_t F₂ γ t:= by


  unfold inverseLaplace_t
  have h_const_ne_zero : (1 / (2 * I * ↑Real.pi) : ℂ) ≠ 0 := by
    simp_all only [one_div, mul_inv_rev, inv_I, ne_eq, neg_eq_zero, mul_eq_zero, inv_eq_zero,
      ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero, OfNat.ofNat_ne_zero, or_self, not_false_eq_true]
  field_simp [h_const_ne_zero]

  calc ∫ (T : ℝ), InverseLaplaceKernel (F₁ + F₂) t γ T
    _=∫ (T : ℝ), (InverseLaplaceKernelFunctT F₁ t γ T +InverseLaplaceKernelFunctT F₂ t γ T ):=by
      congr
      funext T
      simp[InverseLaplaceKernelAdditive F₁ F₂ t]
      have h_eq₁ :InverseLaplaceKernel F₁ t γ T = InverseLaplaceKernelFunctT F₁ t γ T:= by
        simp[InverseLaplaceKernel,InverseLaplaceKernelFunctT]
      have h_eq₂ :InverseLaplaceKernel F₂ t γ T = InverseLaplaceKernelFunctT F₂ t γ T:= by
        simp[InverseLaplaceKernel,InverseLaplaceKernelFunctT]
      simp[h_eq₁]
      simp[h_eq₂]
    _=(∫ T: ℝ, InverseLaplaceKernelFunctT F₁ t γ T) + ∫ T : ℝ, InverseLaplaceKernelFunctT F₂ t γ T:= by
      have h_integrable:= integral_add h₁ h₂
      simp[h_integrable]

theorem inverseLaplaceConst_t(F: ℂ → ℂ) (c:ℂ)(γ t : ℝ)
(h_integrable :  Integrable (InverseLaplaceKernelFunctT F t γ ) volume)
: inverseLaplace_t (c • F) γ t = c* inverseLaplace_t F γ t:= by
  unfold inverseLaplace_t
  have h_const_ne_zero : (1 / (2 * I * ↑Real.pi) : ℂ) ≠ 0 := by
    simp_all only [one_div, mul_inv_rev, inv_I, neg_mul, mul_neg, ne_eq, neg_eq_zero, mul_eq_zero, inv_eq_zero,
      ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero, OfNat.ofNat_ne_zero, or_self, not_false_eq_true]
  field_simp [h_const_ne_zero]

  calc ∫ (T : ℝ), InverseLaplaceKernel (c • F) t γ T
    _=∫ (T : ℝ),( c •(InverseLaplaceKernel F t)) γ T :=by
      congr
      simp[InverseLaplaceKernelConst]
    _=∫ (T : ℝ), c *(InverseLaplaceKernel F t γ T) :=by
      simp_all only [one_div, mul_inv_rev, inv_I, neg_mul, mul_neg, ne_eq, neg_eq_zero, mul_eq_zero, inv_eq_zero,
        ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero, OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Pi.smul_apply,
        smul_eq_mul]
    _=∫ (T : ℝ), c *(InverseLaplaceKernelFunctT F t γ T):= by
      congr
       _ = c * ∫ (T : ℝ), InverseLaplaceKernelFunctT F t γ T := by
      simpa using
        (integral_const_mul c (InverseLaplaceKernelFunctT F t γ))

lemma Fubini_lemma {T t γ : ℝ} {f : ℝ → ℂ} (hMeasurable : Measurable f)
    (h_int : Integrable (fun t => f t * cexp (-(γ * t)))) (hg_Int : Integrable (fun p : ℝ × ℝ => I * cexp ((↑γ + ↑p.1 * I) * ↑t) * cexp (-(↑γ + ↑p.1 * I) * ↑p.2) * f p.2) ((μ_T T).prod μ_real)) :
    ∫ r in Icc (-T) T, I * cexp ((↑γ + ↑r * I) * ↑t) * ∫ (a : ℝ), cexp (-(↑γ + ↑r * I) * ↑a) * f a ∂μ_real =
    ∫ (a : ℝ), (∫ r in Icc (-T) T, I * cexp ((↑γ + ↑r * I) * ↑t) * cexp (-(↑γ + ↑r * I) * ↑a) * f a) ∂μ_real := by
  let g := fun p : ℝ × ℝ => I * cexp ((↑γ + ↑p.1 * I) * ↑t) * cexp (-(↑γ + ↑p.1 * I) * ↑p.2) * f p.2
  have h_replaceg : ∀ r a : ℝ, I * cexp ((↑γ + ↑r * I) * ↑t) * cexp (-(↑γ + ↑r * I) * ↑a) * f a = g (r, a) := by
    intros r a; unfold g; ring_nf

  calc
    ∫ r in Icc (-T) T, I * cexp ((↑γ + ↑r * I) * ↑t) * ∫ (a : ℝ), cexp (-(↑γ + ↑r * I) * ↑a) * f a ∂μ_real =
    ∫ r in Icc (-T) T, (∫ (a : ℝ), I * cexp ((↑γ + ↑r * I) * ↑t) * cexp (-(↑γ + ↑r * I) * ↑a) * f a ∂μ_real) := by
      congr; ext r
      rw [← integral_const_mul (I * cexp ((↑γ + ↑r * I) * ↑t)) (fun a : ℝ => cexp (-(↑γ + ↑r * I) * ↑a) * f a)]
      congr; ext a; rw [← @NonUnitalRing.mul_assoc]
    _ = ∫ r in Icc (-T) T, (∫ (a : ℝ), g (r, a) ∂μ_real) := by
      simp_rw [h_replaceg]
    _ = ∫ (a : ℝ), (∫ (r : ℝ) in Icc (-T) T, g (r, a)) ∂μ_real := by
      have hSfinite : MeasureTheory.SFinite μ_real := by
          unfold μ_real
          infer_instance
      rw [integral_integral_swap hg_Int]

lemma integrand_simplification (t γ T : ℝ) (f: ℝ → ℂ) :
 1 / (2 * I * ↑π) * ∫ (a : ℝ), I * cexp (↑γ * (↑↑t - ↑a)) * f a * (2 * ↑(Real.sin (T * (↑t - a))) / (↑↑t - ↑a)) ∂μ_real =
  ∫ (a : ℝ), f a * cexp (-(↑a - ↑↑t) * ↑γ) *  ↑(Real.sin (T * (↑t - a))) / (↑π*(↑↑t - ↑a)) ∂μ_real:= by calc
  1 / (2 * I * ↑π) * ∫ (a : ℝ), I * cexp (↑γ * (↑↑t - ↑a)) * f a * (2 * ↑(Real.sin (T * (↑t - a))) / (↑↑t - ↑a)) ∂μ_real
  _= ∫ (a : ℝ), 1 / (2 * I * ↑π) * (I * cexp (↑γ * (↑↑t - ↑a)) * f a * (2 * ↑(Real.sin (T * (↑t - a))) / (↑↑t - ↑a)) )∂μ_real:= by
    rw[← integral_const_mul]
  _=∫ (a : ℝ), 1 / (2 * I * ↑π) * (I * cexp (↑γ * (↑↑t - ↑a)) * f a * 2 * ↑(Real.sin (T * (↑t - a))) / (↑↑t - ↑a) )∂μ_real:= by
    congr
    ext a
    ring_nf

  _=∫ (a : ℝ), 1 / (2 * I * ↑π) * (2 *I * cexp (↑γ * (↑↑t - ↑a)) * f a * ↑(Real.sin (T * (↑t - a))) / (↑↑t - ↑a) )∂μ_real:= by
    congr
    ext a
    ring_nf

  _=∫ (a : ℝ),  1 / (2 * I * ↑π) * (2*I) * (cexp (↑γ * (↑↑t - ↑a)) * f a * ↑(Real.sin (T * (↑t - a))) / (↑↑t - ↑a) )∂μ_real:= by
    congr
    ext a
    ring
  _=∫ (a : ℝ), 1 / (↑π) * (cexp (↑γ * (↑↑t - ↑a)) *   f a * ↑(Real.sin (T * (↑t - a))) / (↑↑t - ↑a) )∂μ_real:= by
    congr
    ext a
    have h_const : 1 / (2 * I * ↑π) * (2 * I) = 1 / ↑π := by
      field_simp [I_ne_zero, Real.pi_ne_zero]
    rw[h_const]
  _=∫ (a : ℝ), f a * cexp (-(↑a - ↑↑t) * ↑γ) *  ↑(Real.sin (T * (↑t - a))) / (↑π*(↑↑t - ↑a))   ∂μ_real:= by
    congr
    ext a
    field_simp
    ring_nf

lemma integral_sinc_equivalence
  (f : ℝ → ℂ) (t T γ : ℝ) (μ_real : Measure ℝ) [NoAtoms μ_real] :
  (∫ (a : ℝ), f a * cexp (-(↑a - ↑t) * ↑γ) * ↑(Real.sin (T * (t - a))) / (↑π * (↑t - ↑a)) ∂μ_real) =
  (∫ (a : ℝ), f a * cexp (-(↑a - ↑t) * ↑γ) * ↑T * ↑(sinc (T * (t - a))) / ↑π ∂μ_real) := by

  apply integral_congr_ae
  have h_ae : ∀ᵐ a ∂μ_real, a ≠ t := by
    simp [ae_iff, MeasureTheory.NoAtoms.measure_singleton]

  filter_upwards [h_ae] with a ha
  have: t-a≠ 0 := sub_ne_zero.mpr ha.symm

  field_simp [this]
  unfold sinc
  by_cases hT : T = 0
  · simp[hT]
  · have h_arg : T * (t - a) ≠ 0 := mul_ne_zero hT this
    rw [if_neg h_arg]
    push_cast
    field_simp
    by_cases hf : f a = 0
    · simp[hf]
    · have h_diff : ↑t - ↑a ≠ (0 : ℂ) := by
        norm_cast
      have h_diff_T :   ↑T ≠ (0 : ℂ):= by
        norm_cast

      field_simp [sub_ne_zero.mpr ha.symm, h_arg]

lemma h2ndIntegralCalc  (f: ℝ → ℂ)(γ T: ℝ)(S: Set ℝ)
(hT : 0 ≤ T) :∀ t∈ S,
   ∫ (a : ℝ), I * cexp (↑γ * (↑↑t - ↑a)) * f a *
   ( ∫ (r : ℝ) in Icc (-T) T, cexp (I * ↑r * (↑↑t - ↑a)) )∂μ_real=
    ∫ (a : ℝ),I*cexp (↑γ * (↑↑t-↑a))*f a*
    ( 2 * Real.sin (T * (t - a)) / (t - a))∂μ_real := by
      intro t h_tS
      apply integral_congr_ae
      have h_a_neq_t : ∀ (a:ℝ), a ≠ t →
      (I * cexp (↑γ * (↑↑t - ↑a)) * f a * ∫ (r : ℝ) in Icc (-T) T, cexp (I * ↑r * (↑↑t - ↑a))) =
      (I * cexp (↑γ * (↑↑t - ↑a)) * f a * (2 * Real.sin (T * (t - a)) / (t - a))) := by
        intro a  ha_neq_t
        rw [integral_cexp_Icc_Dirichlet]
        have: (t : ℝ) - a ≠ 0 := by
          intro h
          apply ha_neq_t
          have: t = a := by
            have : (t : ℝ) = a := by linarith
            apply this
          symm
          exact this
        simp [this]
        apply hT
      rw [Filter.EventuallyEq, ae_iff]
      have : NoAtoms μ_real:= by
        unfold μ_real
        infer_instance

      refine measure_mono_null ?_ (measure_singleton (t : ℝ))
      intro a ha_error
      contrapose! ha_error
      have h_a_not_eq_t_by_contra : a ≠ t :=by
        simpa [Set.mem_singleton_iff] using ha_error
      rw [Set.mem_setOf_eq]
      have eq := h_a_neq_t a h_a_not_eq_t_by_contra
      simp [eq]

theorem IsInverseLaplaceBounded  (f: ℝ → ℂ)(γ T: ℝ)(S: Set ℝ)
(h_cont : Continuous (f))
(h_int: Integrable (fun t ↦ (f t )*cexp (-(γ*t))))
(hMeasurable: Measurable f)
(h_Laplace_int: ∀ t∈ S, Integrable ((InverseLaplaceKernelFunctT (RealLaplaceTransform f) t) γ ) volume)
(h_diff : Differentiable ℝ f)
(h_diff_int: Integrable (fun t ↦ (deriv f t )*cexp (-γ*t)))
(hT : 0 ≤ T):
∀(t:S), (inverseLaplaceFunctionBounded (RealLaplaceTransform f) γ T S h_Laplace_int) t =  ∫ (a : ℝ), f a * cexp (-(↑a - ↑↑t) * ↑γ) *  T* ↑(Real.sinc (T * (↑t - a))) / (↑π)  ∂μ_real:= by
  unfold inverseLaplaceFunctionBounded
  unfold inverseLaplace_tBounded
  unfold InverseLaplaceKernel
  intro t
  have :  ∫ (r : ℝ) in Icc (-T) T, I * cexp (imNbFromReals γ r * ↑↑t) *
          RealLaplaceTransform f (imNbFromReals γ r) =
    ∫ (r : ℝ) in Icc (-T) T, I * cexp (imNbFromReals γ r * ↑↑t) *
          ∫a,cexp (-imNbFromReals γ r *a) * (f a) ∂μ_real:= by
      congr
      ext T
      simp only [neg_mul, mul_eq_mul_left_iff, mul_eq_zero, I_ne_zero, Complex.exp_ne_zero, or_self,
        or_false]
      rw[RealLaplaceTransformIs f hMeasurable (imNbFromReals γ  T)]
      simp only [neg_mul]
  rw[this]
  unfold imNbFromReals

  let g:= fun p: ℝ × ℝ ↦  I * cexp ((↑γ + (↑p.1) * I) * (↑↑t))* cexp (-(↑γ + (↑p.1) * I) * (↑p.2))* f p.2
  let φ :=
    fun r : ℝ =>
      I * cexp ((↑γ + (↑r) * I) * (↑↑t))

  let ψ :=
    fun a : ℝ =>
      cexp (-↑γ * ↑a) * f a

  -- ψ is integrable by h_int
  have hψ : Integrable ψ μ_real := by
    have h_simp_phi: ψ =  fun a : ℝ => (f a )*cexp (-(↑γ * ↑a)):= by
      simp[ψ]
      simp [ mul_comm]
    simp[h_simp_phi]
    apply Integrable.mono_measure (μ := μ_real) (ν := volume)
    case h=>
      exact h_int
    unfold μ_real
    exact Measure.restrict_le_self

  have hφ_cont : Continuous φ := by
    unfold φ
    continuity

  have hφ_bdd :
      ∃ C, 0 ≤ C ∧ ∀ r ∈ Icc (-T) T, ‖φ r‖ ≤ C := by
    have K : IsCompact (Icc (-T) T) := isCompact_Icc
    have hcont : ContinuousOn φ (Icc (-T) T) := hφ_cont.continuousOn
    rcases K.exists_bound_of_continuousOn hcont with ⟨C, hC⟩
    let C' := max C 0
    refine ⟨C', le_max_right _ _, ?_⟩
    intro r hr
    calc
    ‖φ r‖ ≤ C := hC r hr
    _ ≤ C' := le_max_left C 0

  have hg_Int : Integrable g ((μ_T T).prod μ_real) := by
    have h_norm_g : ∀ r a, ‖g (r, a)‖ = ‖f a * cexp (↑γ * (↑t - ↑a))‖ := by
      intro r a
      unfold g
      simp
      rw [Complex.norm_exp, Complex.norm_exp]
      have :  ‖f a‖* ‖cexp (↑γ * (↑↑t - ↑a))‖= ‖cexp (↑γ * (↑↑t - ↑a))‖* ‖f a‖ := by
        rw [@NonUnitalNormedCommRing.mul_comm]
      rw[this]
      congr 1
      rw[Complex.norm_exp]
      have :  ((↑γ + ↑r * I) * ↑↑t).re =  ↑γ*↑↑t:= by
        simp
      rw[this]
      have : ((-(↑r * I) + -↑γ) * ↑a).re = -↑γ* ↑a:= by
        simp
      rw[this]
      calc  rexp (γ * ↑t) * rexp (-γ * a)
        _=  rexp (γ * ↑t+-γ* a):= by rw [Real.exp_add]
        _= rexp (γ *( ↑t- a)):= by
          simp only [exp_eq_exp]
          rw [@neg_mul]
          rw [@neg_mul_eq_mul_neg]
          rw[← mul_add γ (↑t) (-a)]
          rfl
      simp

    have hg_meas : Measurable g := by
      unfold g
      refine Measurable.mul ?_ (Measurable.comp hMeasurable (measurable_snd))
      apply Measurable.mul
      apply Measurable.mul
      · exact measurable_const
      · apply Continuous.measurable
        continuity
      apply Continuous.measurable
      apply Continuous.cexp
      apply Continuous.mul
      · apply Continuous.neg
        apply Continuous.add
        · continuity
        · apply Continuous.mul
          ·refine Continuous.fst' ?_;
            apply Complex.continuous_ofReal
          ·exact continuous_const
      · refine Continuous.snd' ?_;
        apply Complex.continuous_ofReal

    have hSfinite : MeasureTheory.SFinite μ_real := by
          unfold μ_real
          infer_instance
    rw [integrable_prod_iff]
    refine ⟨?_, ?_⟩

    · apply ae_of_all
      intro r
      unfold g
      simp only [mul_assoc]
      apply Integrable.const_mul
      apply Integrable.const_mul
      rw[← integrable_norm_iff]
      simp_rw [norm_mul, Complex.norm_exp]
      have h_re : ∀ (a : ℝ), (-(↑γ + ↑r * I) * ↑a).re = -γ * a := by
        intro a
        simp
      simp_rw [h_re]
      have h_norm_eq : (fun a ↦ rexp (-γ * a) * ‖f a‖) = (fun a ↦ ‖f a * cexp (-γ * a)‖) := by
          ext a; simp [ Complex.norm_exp, mul_comm]
      simp_rw[h_norm_eq]
      simp only [neg_mul]
      rw[integrable_norm_iff]
      have hμ : μ_real ≤ volume:= by
        unfold μ_real
        exact Measure.restrict_le_self
      apply Integrable.mono_measure h_int hμ
      apply Measurable.aestronglyMeasurable
      apply Measurable.mul
      · exact hMeasurable
      · apply Continuous.measurable
        apply Continuous.cexp
        apply Continuous.neg
        apply Continuous.mul
        · exact continuous_const
        · exact Complex.continuous_ofReal

      apply Measurable.aestronglyMeasurable
      apply Measurable.mul
      · apply Continuous.measurable
        apply Continuous.cexp
        apply Continuous.mul
        · exact continuous_const
        · exact Complex.continuous_ofReal
      exact hMeasurable


    · simp_rw[h_norm_g]
      have hμTFinite : IsFiniteMeasure (μ_T T) := by
          unfold μ_T
          infer_instance
      apply integrable_const
    apply Measurable.aestronglyMeasurable
    exact hg_meas

  rw [Fubini_lemma hMeasurable h_int hg_Int]

  have hOutIntegral: ∀a : ℝ,
  ∫ (r : ℝ) in Icc (-T) T, I * cexp ((↑γ + ↑r * I) * ↑↑t) * cexp (-(↑γ + ↑r * I) * ↑a) * f a=
  I*cexp (↑γ * (↑↑t-↑a))*f a*(∫ (r : ℝ) in Icc (-T) T,  cexp (I*↑r * (↑↑t-↑a))) := by
    intro a
    calc ∫ r in Icc (-T) T, I * cexp ((↑γ + ↑r * I) * ↑↑t) * cexp (-(↑γ + ↑r * I) * ↑a) * f a
    _=∫ (r : ℝ) in Icc (-T) T,  I* cexp (↑γ * (↑↑t-↑a)) * cexp (I*↑r * (↑↑t-↑a)) * f a :=by
      congr
      ext r
      have hDevExp : cexp ((↑γ + ↑r * I) * ↑↑t) * cexp (-(↑γ + ↑r * I) * ↑a)= cexp (↑γ * (↑↑t-↑a)) * cexp (I*↑r * (↑↑t-↑a)) := by
        calc cexp ((↑γ + ↑r * I) * ↑↑t) * cexp (-(↑γ + ↑r * I) * ↑a)
        _= cexp (↑γ * ↑↑t + ↑r * I * ↑↑t)* cexp (-(↑γ + ↑r * I) * ↑a):= by
          simp
          rw [@NonUnitalNonAssocRing.right_distrib]
        _=cexp (↑γ * ↑↑t)* cexp (↑r * I * ↑↑t)* cexp (-(↑γ + ↑r * I) * ↑a):= by
          simp
          rw [Complex.exp_add]
        _=cexp (↑γ * ↑↑t)* cexp (↑r * I * ↑↑t)*cexp (-↑r * I * ↑a) * cexp (-↑γ * ↑a):= by
          simp
          rw [@NonUnitalNonAssocRing.right_distrib]
          rw [Complex.exp_add]
          simp
          ac_rfl
        _=cexp (↑γ * ↑↑t) * cexp (↑r * I * ↑↑t) * cexp (-↑γ * ↑a) * cexp (-↑r * I * ↑a) := by
          simp
          ring
        _=cexp (↑γ * ↑↑t) * cexp (-↑γ * ↑a) *cexp (↑r * I * ↑↑t) * cexp (-↑r * I * ↑a):= by
          ring
        _= cexp (↑γ * ↑↑t-↑γ * ↑a) *cexp (↑r * I * ↑↑t) * cexp (-↑r * I * ↑a):= by
          rw [←Complex.exp_add]
          ring_nf
        _= cexp (↑γ * (↑↑t-  ↑a)) *cexp (↑r * I * ↑↑t) * cexp (-↑r * I * ↑a):= by
          ring_nf
        _=cexp (↑γ * (↑↑t-  ↑a)) *(cexp (↑r * I * ↑↑t) * cexp (-↑r * I * ↑a)):= by
          ring_nf
        _=cexp (↑γ * (↑↑t-  ↑a)) *(cexp (I* ↑r *(↑↑t- ↑a))):= by
          have h_eq: cexp (↑r * I * ↑↑t) * cexp (-↑r * I * ↑a)= cexp (I* ↑r *(↑↑t- ↑a)):= by
            rw [← Complex.exp_add]
            ring_nf
          rw[h_eq]
        _=cexp (↑γ * (↑↑t-  ↑a)) *cexp (I* ↑r *(↑↑t- ↑a)):= by
          ring_nf
      calc I * cexp ((↑γ + ↑r * I) * ↑↑t) * cexp (-(↑γ + ↑r * I) * ↑a) * f a
      _=I * (cexp ((↑γ + ↑r * I) * ↑↑t) * cexp (-(↑γ + ↑r * I) * ↑a)) * f a:= by
        ring_nf
      _=I * (cexp (↑γ * (↑↑t-↑a)) * cexp (I*↑r * (↑↑t-↑a))) * f a := by
        rw[hDevExp]
      _=I * cexp (↑γ * (↑↑t - ↑a)) * cexp (I * ↑r * (↑↑t - ↑a)) * f a:= by
        ring_nf
    _=∫ (r : ℝ) in Icc (-T) T,  I* cexp (↑γ * (↑↑t-↑a)) * (cexp (I*↑r * (↑↑t-↑a)) * f a):= by
      congr
      ext r
      ring_nf
    _=∫ (r : ℝ) in Icc (-T) T,  I* cexp (↑γ * (↑↑t-↑a)) * (f a * cexp (I*↑r * (↑↑t-↑a))):= by
      congr
      ext r
      ring
    _=∫ (r : ℝ) in Icc (-T) T,  I* cexp (↑γ * (↑↑t-↑a)) * f a * cexp (I*↑r * (↑↑t-↑a)):= by
      congr
      ext r
      ring
    _=∫ (r : ℝ) in Icc (-T) T,  (I* cexp (↑γ * (↑↑t-↑a)) * f a )* cexp (I*↑r * (↑↑t-↑a)):= by
      congr
    _=(I* cexp (↑γ * (↑↑t-↑a)) * f a )  * ∫ (r : ℝ) in Icc (-T) T,  cexp (I*↑r * (↑↑t-↑a)):= by
      rw[MeasureTheory.integral_const_mul]
    _=I* cexp (↑γ * (↑↑t-↑a)) * f a   * ∫ (r : ℝ) in Icc (-T) T,  cexp (I*↑r * (↑↑t-↑a)):= by
      ring


  have hOutIntegralTot:
    ∫ (a : ℝ), (∫ (r : ℝ) in Icc (-T) T, I * cexp ((↑γ + ↑r * I) * ↑↑t) * cexp (-(↑γ + ↑r * I) * ↑a) * f a )∂μ_real =
    ∫ (a : ℝ),I*cexp (↑γ * (↑↑t-↑a))*f a*(∫ (r : ℝ) in Icc (-T) T,  cexp (I*↑r * (↑↑t-↑a)))∂μ_real := by
    congr
    simp_rw[hOutIntegral]

  simp_rw[hOutIntegralTot]
  have h:= h2ndIntegralCalc f γ T S hT
  rw[h]
  rw[integrand_simplification t γ T f ]
  have : NoAtoms μ_real:= by
        unfold μ_real
        infer_instance
  rw[integral_sinc_equivalence f t T γ μ_real]
  exact t.2

lemma DirichletSinDerivAt(T : ℝ)(S: Set ℝ) (t:S) :  ∀ a, deriv (fun a : ℝ ↦ DirichletSin (T * (a - t))) a =  T* (Real.sinc (T * (t - a))) / π  := by
  intro a
  have hasDerivAt_DirichletSin: ∀x:ℝ , HasDerivAt DirichletSin (sinc x / π) x := by
    intro x
    unfold DirichletSin
    apply HasDerivAt.const_add
    have: (sinc x / π)= 1/π * sinc x:= by field_simp
    rw[this]
    apply HasDerivAt.const_mul (1/π)
    apply intervalIntegral.integral_hasDerivAt_right
    exact continuous_sinc.intervalIntegrable 0 x
    exact continuous_sinc.stronglyMeasurableAtFilter _ _
    exact continuous_sinc.continuousAt
  let v1 := fun x : ℝ ↦ T * (x - t)
  have h_comp : HasDerivAt (fun x ↦ DirichletSin (v1 x)) ((sinc (v1 a) / π) * T) a := by
    apply HasDerivAt.comp a (hasDerivAt_DirichletSin (v1 a))
    simp only [v1]
    have h_linear : HasDerivAt (fun x ↦ T * (x - t)) T a := by
      have: T = T*1:= by simp
      rw[this]
      have: (fun x ↦ T *1*  (x - ↑t))= fun x ↦ T *  (x - ↑t):=by
        funext x
        simp
      rw[this]
      apply HasDerivAt.const_mul (T)
      apply HasDerivAt.sub_const
      apply hasDerivAt_id a
    exact h_linear
  unfold v1 at h_comp
  rw [h_comp.deriv]
  field_simp
  by_cases hT: T=0
  · simp
    right
    exact hT
  · field_simp[hT]
    rw [← Real.sinc_neg]
    ring_nf

lemma CExpDerivAt(f: ℝ → ℂ) (γ: ℝ) (S: Set ℝ) (t:S) (h_diff : Differentiable ℝ f) : ∀ a, HasDerivAt (fun a : ℝ ↦ f a * cexp (-(a - t) * γ)) (deriv f a * cexp (-(a - t) * γ) - f a * γ * cexp (-(a - t) * γ)) a := by
  intro a
  let u' := deriv f a
  let v := cexp (-(a - t) * γ)
  have h_deriv_exp : HasDerivAt (fun x:ℝ↦ cexp (-(↑x - (t:ℂ)) * (γ:ℂ))) (-(γ:ℂ) * cexp (-( ↑a - (t:ℂ)) * (γ:ℂ))) a := by
    have hg : HasDerivAt (fun x ↦ -(x - t) * (γ:ℂ)) (-(γ : ℂ)) a := by
      have: -(γ : ℂ)= -1* (γ : ℂ):= by simp
      rw[this]
      apply HasDerivAt.mul_const
      apply HasDerivAt.neg
      apply HasDerivAt.sub_const
      apply hasDerivAt_id
    have:= hg.cexp
    have h_real := this.comp_ofReal
    rw [mul_comm] at h_real
    exact h_real

  have h_prod := (h_diff a).hasDerivAt.mul h_deriv_exp
  convert h_prod using 1
  ring_nf

lemma h_lim_CexpTop (f : ℝ → ℂ) (γ T : ℝ)(S: Set ℝ)(t:S)
  (h_diff : Differentiable ℝ f)
  (h_int : Integrable (fun t ↦ f t * cexp (-γ * t)))
  (h_diff_int : Integrable (fun t ↦ (deriv f t) * cexp (-γ * t))) : Tendsto ((fun a : ℝ ↦ f a * cexp (-(a - t) * γ))) atTop (𝓝 0) := by
  have h_rew : ∀ a, f a * cexp (-(↑a - ↑↑t) * ↑γ) = (f a * cexp (-(↑a * ↑γ))) * cexp (↑↑t * ↑γ) := by
    intro a
    ring_nf
    rw [Complex.exp_add]
    ring
  simp_rw [h_rew]
  have h_int_new := h_int.integrableOn (s := Set.Ici 0)

  apply MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
  · intro x hx
    have h:= CExpDerivAt f γ S t h_diff x
    convert h using 1
    funext a
    have:  f a * cexp (-(↑a * ↑γ)) * cexp (↑↑t * ↑γ)=  f a *cexp (-(↑a * ↑γ)+↑↑t * ↑γ):= by
      by_cases h_f: f a =0
      simp[h_f]
      field_simp
      rw [← Complex.exp_add]
      ring_nf
    rw[this]
    by_cases h_f: f a =0
    simp[h_f]
    field_simp
    ring_nf
  · apply Integrable.sub
    · have h_rew1 : ∀ x, deriv f x * cexp (-(↑x - ↑↑t) * ↑γ) = (deriv f x * cexp (-↑x * ↑γ)) * cexp (↑↑t * ↑γ) := by
        intro x; ring_nf; rw [Complex.exp_add]; ring
      simp_rw [h_rew1]
      apply Integrable.mul_const
      have: (fun x ↦ deriv f x * cexp (-↑x * ↑γ))= fun x ↦ deriv f x * cexp (-↑γ* ↑x ):= by
        funext x
        simp
        by_cases h_f: deriv f x =0
        right
        exact h_f
        left
        ring_nf
      rw[this]
      exact h_diff_int.integrableOn
    · have: (fun x ↦ f x * ↑γ * cexp (-(↑x - ↑↑t) * ↑γ))= fun x ↦  ↑γ* (f x  * cexp (-(↑x - ↑↑t) * ↑γ)):= by
        funext x
        simp
        ring
      rw[this]
      refine Integrable.const_mul (f := fun x ↦ f x * cexp (-(↑x - ↑↑t) * ↑γ)) ?_ (↑γ)
      have h_rew2 : ∀ x, f x * cexp (-(↑x - ↑↑t) * ↑γ) = (f x * cexp (-↑x * ↑γ)) * cexp (↑↑t * ↑γ) := by
        intro x; ring_nf; rw [Complex.exp_add]; ring
      simp_rw [h_rew2]
      apply Integrable.mul_const
      have: (fun x ↦ f x * cexp (-↑x * ↑γ))= fun x ↦ f x * cexp (-↑γ* ↑x ):= by
        funext x
        simp
        by_cases h_f: f x =0
        right
        exact h_f
        left
        ring_nf
      rw[this]
      exact h_int.integrableOn
  · rw [IntegrableOn]
    apply Integrable.mul_const
    have: (fun x ↦ f x * cexp (-(↑x * ↑γ)))=fun x ↦ f x * cexp (-↑γ * ↑x):=by
      funext x
      by_cases h_f: f x =0
      simp[h_f]
      field_simp[h_f]
    simp_rw[this]
    have h_int_new2 := h_int.integrableOn (s := Set.Ioi 0)
    rw [IntegrableOn] at h_int_new2
    exact h_int_new2

lemma h_lim_CexpBot (f : ℝ → ℂ) (γ T : ℝ)(S: Set ℝ)(t:S)
  (h_diff : Differentiable ℝ f)
  (h_int : Integrable (fun t ↦ f t * cexp (-γ * t)))
  (h_diff_int : Integrable (fun t ↦ (deriv f t) * cexp (-γ * t))) : Tendsto ((fun a : ℝ ↦ f a * cexp (-(a - t) * γ))) atBot (𝓝 0) := by
  have h_rew : ∀ a, f a * cexp (-(↑a - ↑↑t) * ↑γ) = (f a * cexp (-(↑a * ↑γ))) * cexp (↑↑t * ↑γ) := by
    intro a
    ring_nf
    rw [Complex.exp_add]
    ring
  simp_rw [h_rew]
  have h_int_new := h_int.integrableOn (s := Set.Iic 0)

  apply MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
  · intro x hx
    have h:= CExpDerivAt f γ S t h_diff x
    convert h using 1
    funext a
    have:  f a * cexp (-(↑a * ↑γ)) * cexp (↑↑t * ↑γ)=  f a *cexp (-(↑a * ↑γ)+↑↑t * ↑γ):= by
      by_cases h_f: f a =0
      simp[h_f]
      field_simp
      rw [← Complex.exp_add]
      ring_nf
    rw[this]
    by_cases h_f: f a =0
    simp[h_f]
    field_simp
    ring_nf
  · apply Integrable.sub
    · have h_rew1 : ∀ x, deriv f x * cexp (-(↑x - ↑↑t) * ↑γ) = (deriv f x * cexp (-↑x * ↑γ)) * cexp (↑↑t * ↑γ) := by
        intro x; ring_nf; rw [Complex.exp_add]; ring
      simp_rw [h_rew1]
      apply Integrable.mul_const
      have: (fun x ↦ deriv f x * cexp (-↑x * ↑γ))= fun x ↦ deriv f x * cexp (-↑γ* ↑x ):= by
        funext x
        simp
        by_cases h_f: deriv f x =0
        right
        exact h_f
        left
        ring_nf
      rw[this]
      exact h_diff_int.integrableOn
    · have: (fun x ↦ f x * ↑γ * cexp (-(↑x - ↑↑t) * ↑γ))= fun x ↦  ↑γ* (f x  * cexp (-(↑x - ↑↑t) * ↑γ)):= by
        funext x
        simp
        ring
      rw[this]
      refine Integrable.const_mul (f := fun x ↦ f x * cexp (-(↑x - ↑↑t) * ↑γ)) ?_ (↑γ)
      have h_rew2 : ∀ x, f x * cexp (-(↑x - ↑↑t) * ↑γ) = (f x * cexp (-↑x * ↑γ)) * cexp (↑↑t * ↑γ) := by
        intro x; ring_nf; rw [Complex.exp_add]; ring
      simp_rw [h_rew2]
      apply Integrable.mul_const
      have: (fun x ↦ f x * cexp (-↑x * ↑γ))= fun x ↦ f x * cexp (-↑γ* ↑x ):= by
        funext x
        simp
        by_cases h_f: f x =0
        right
        exact h_f
        left
        ring_nf
      rw[this]
      exact h_int.integrableOn
  · rw [IntegrableOn]
    apply Integrable.mul_const
    have: (fun x ↦ f x * cexp (-(↑x * ↑γ)))=fun x ↦ f x * cexp (-↑γ * ↑x):=by
      funext x
      by_cases h_f: f x =0
      simp[h_f]
      field_simp[h_f]
    simp_rw[this]
    have h_int_new2 := h_int.integrableOn (s := Set.Iic 0)
    rw [IntegrableOn] at h_int_new2
    exact h_int_new2

theorem IsInverseLaplaceBounded' (f : ℝ → ℂ) (γ T : ℝ)(S: Set ℝ)
  (h_cont : Continuous f)
  (h_diff : Differentiable ℝ f)
  (h_int : Integrable (fun t ↦ f t * cexp (-γ * t)))
  (h_diff_int : Integrable (fun t ↦ (deriv f t) * cexp (-γ * t)))
  (hT : 0 ≤ T) :
  ∀(t:S), ∫ (a : ℝ), f a * cexp (-(↑a - ↑↑t) * ↑γ) *  T* ↑(Real.sinc (T * (↑t - a))) / (↑π) ∂μ_real =
    -f 0 * cexp (↑↑t * ↑γ) * ↑(DirichletSin (-T * ↑t)) -∫ (a : ℝ), deriv (fun u ↦ f u * cexp (-(u - t) * γ)) a * DirichletSin (T * (a - t)) ∂μ_real  := by
  intro t
  let u := fun a : ℝ ↦ f a * cexp (-(a - t) * γ)
  let v := fun a : ℝ ↦ DirichletSin (T * (a - t))
  have h_deriv_v : ∀ a, deriv v a =  T* (Real.sinc (T * (t - a))) / π  := by
    exact DirichletSinDerivAt T S t
  have h_has_deriv_u : ∀ a, HasDerivAt u (deriv f a * cexp (-(a - t) * γ) - f a * γ * cexp (-(a - t) * γ)) a := by
    exact CExpDerivAt f γ S t h_diff

  let t_real : ℝ := ↑↑t
  have h_deriv_u_eq : ∀ a, deriv u a = deriv f a * cexp (-(a - t_real) * γ) - f a * γ * cexp (-(a - t_real) * γ) := by
    intro a
    exact (h_has_deriv_u a).deriv

  have h_lim_u_Top : Tendsto u atTop (𝓝 0) := by
    exact h_lim_CexpTop f γ T S t h_diff h_int h_diff_int

  have h_lim_u_Bot : Tendsto u atBot (𝓝 0) := by
    exact h_lim_CexpBot f γ T S t h_diff h_int h_diff_int

  have h_v_real_bdd : ∃ C, ∀ x, |v x| ≤ C :=  DirichletSinBoundedComp T t hT

  obtain ⟨C, hC⟩ := h_v_real_bdd
  let vC := fun a ↦ (v a : ℂ)
  have h_v_bdd_top : IsBoundedUnder (· ≤ ·) atTop (norm ∘ vC) := by
    refine ⟨C, eventually_atTop.mpr ⟨0, fun x _ ↦ ?_⟩⟩
    specialize hC x
    simp only [vC, Function.comp_apply, Complex.norm_real]
    simp [Real.norm_eq_abs, hC]

  have h_v_bdd_bot : IsBoundedUnder (· ≤ ·) atBot (norm ∘ vC) := by
    refine ⟨C, eventually_atBot.mpr ⟨0, fun x _ ↦ ?_⟩⟩
    simp only [vC, Function.comp_apply, Complex.norm_real]
    exact hC x

  have h_uv_top : Tendsto (fun a ↦ u a * v a) atTop (𝓝 0) :=
  NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded h_lim_u_Top h_v_bdd_top

  have h_uv_bot : Tendsto (fun a ↦ u a * (v a : ℂ)) atBot (𝓝 0) :=
  NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded h_lim_u_Bot h_v_bdd_bot

  have h_prep : ∫ (a : ℝ), f a * cexp (-(↑a - ↑↑t) * ↑γ) * ↑T * ↑(sinc (T * (↑t - a))) / ↑π ∂μ_real=
              ∫ (a : ℝ), u a * ↑(deriv v a) ∂μ_real:= by
    congr
    funext a
    unfold u
    rw [ h_deriv_v]
    field_simp
    by_cases h_f_0: (f a )= 0
    · simp[h_f_0]
    · field_simp[h_f_0]
      rw [Complex.ofReal_div]
      field_simp [Real.pi_ne_zero]
      rw [Complex.ofReal_mul]
  rw[h_prep]
  have h_deriv_u_v : ∀ a, deriv u a * v a = (deriv f a * cexp (-(↑a - ↑↑t) * ↑γ) - f a * ↑γ * cexp (-(↑a - ↑↑t) * ↑γ)) * DirichletSin (T * (a - ↑t)) := by
    intro a
    rw [h_deriv_u_eq]

  have h_int_u'v : Integrable (fun a => deriv u a * ↑(v a)) := by
    simp_rw [h_deriv_u_eq]
    simp_rw [sub_mul]
    apply Integrable.sub
    · have h_int_shifted : Integrable (fun a ↦ (deriv f a * cexp (-(↑a - ↑t_real) * ↑γ))) := by
        have:(fun a ↦ (deriv f a * cexp (-(↑a - ↑t_real) * ↑γ))) = fun x ↦ deriv f x * cexp (- ↑γ* ↑x) * cexp (↑t_real * ↑γ) := by
          funext x
          ring_nf
          rw[Complex.exp_add]
          field_simp
        rw[this]
        apply Integrable.mul_const
        exact h_diff_int
      unfold v
      exact Integrable_DirichletSin_times_integrableFunction' (fun a ↦ (deriv f a * cexp (-(↑a - ↑t_real) * ↑γ))) T t hT h_int_shifted
    · have h_int_f_shifted : Integrable (fun a ↦ (f a * ↑γ * cexp (-(↑a - ↑t_real) * ↑γ))) := by
        have:(fun a ↦ (f a * ↑γ* cexp (-(↑a - ↑t_real) * ↑γ))) = fun x ↦ ↑γ*f x * cexp (- ↑γ* ↑x) * cexp (↑t_real * ↑γ) := by
          funext x
          simp_rw [neg_sub]
          have: cexp ((↑t_real - ↑x) * ↑γ)= cexp (↑t_real* ↑γ - ↑x* ↑γ):= by
            ring_nf
          rw[this]
          rw[Complex.exp_sub]
          field_simp
          have: cexp (↑γ * ↑x) * cexp (-(↑γ * ↑x))=1 := by
            rw [← Complex.exp_add]
            ring_nf
            rw[Complex.exp_zero]
          by_cases h_f: f x =0
          simp[h_f]
          by_cases h_gamma: γ =0
          simp[h_gamma]
          field_simp[h_f,h_gamma]
          rw[this]
        rw[this]
        apply Integrable.mul_const
        have: (fun x ↦ ↑γ * f x * cexp (-↑γ * ↑x))= fun x ↦ ↑γ *( f x * cexp (-↑γ * ↑x)):= by
          funext x
          ring_nf
        rw[this]
        apply Integrable.const_mul (f:= fun x ↦ f x * cexp (-↑γ * ↑x)) (c:=↑γ)
        exact h_int

      apply MeasureTheory.Integrable.mul_bdd
      · exact h_int_f_shifted
      · apply Continuous.aestronglyMeasurable
        unfold v
        have := DirichletSin_continuous_comp T t
        exact continuous_ofReal.comp this
      · apply ae_of_all
        intro a
        rw [Complex.norm_real]
        rw [Real.norm_eq_abs]
        exact hC a

  have h_int_uv' : Integrable (fun a => u a * ↑(deriv v a)) := by
    simp_rw [h_deriv_v]
    have : (fun a ↦ u a * ↑(T * sinc (T * (↑t - a)) / π))= fun a ↦ u a * ↑( sinc (T * (↑t - a)))* (T / π):= by
      funext a
      simp_rw [mul_div_assoc]
      by_cases h_u_z: u a =0
      simp[h_u_z]
      field_simp[h_u_z]
      simp[pi_ne_zero]
      ring_nf
    rw[this]
    apply Integrable.mul_const
    apply MeasureTheory.Integrable.mul_bdd
    · unfold u
      have: (fun a ↦ f a * cexp (-(↑a - ↑↑t) * ↑γ))= (fun a ↦ f a *cexp (-↑γ *↑a ) * cexp (↑γ*↑t ) ):= by
        funext a
        by_cases h_f_z: f a =0
        simp[h_f_z]
        field_simp[h_f_z]
        have h : cexp (-((↑a - ↑↑t) * ↑γ)) =  cexp (-(↑a * ↑γ)) * cexp (↑↑t * ↑γ):= by
          ring
          rw[Complex.exp_add]
        rw[h]
      rw[this]
      apply Integrable.mul_const
      exact h_int
    · apply Continuous.aestronglyMeasurable
      have: Continuous fun x ↦ sinc (T * (↑t - x)):= by
        have: Continuous fun x ↦ T * (↑t - x):= by
          ring_nf
          apply Continuous.sub
          continuity
          continuity
        exact continuous_sinc.comp this
      exact continuous_ofReal.comp this
    · apply ae_of_all
      intro a
      norm_cast
      exact Real.abs_sinc_le_one (T * (t_real - a))

  have h_u_deriv_eq : ∀ a, HasDerivAt u (deriv u a) a := by
    intro a
    apply DifferentiableAt.hasDerivAt
    exact (h_has_deriv_u a).differentiableAt
  have h_v_deriv_eq : ∀ a, HasDerivAt (fun x ↦ ↑(v x)) (↑(deriv v a)) a := by
    have h_v_diff : ∀ a, DifferentiableAt ℝ v a := by
      intro a
      unfold v
      unfold DirichletSin
      apply DifferentiableAt.add
      · exact differentiableAt_const (1 / 2)
      · apply DifferentiableAt.mul
        · exact differentiableAt_const (1 / π)
        · let g := fun (x : ℝ) ↦ ∫ (t : ℝ) in 0..x, sinc t
          let f := fun (a : ℝ) ↦ T * (a - t_real)
          apply DifferentiableAt.comp (x := a) (g := fun x ↦ ∫ (t : ℝ) in 0..x, sinc t) (f := fun a ↦ T * (a - t_real))
          · apply HasDerivAt.differentiableAt
            apply (intervalIntegral.integral_hasDerivAt_right ?_ ?_)
            exact Real.continuous_sinc.continuousAt
            exact Real.continuous_sinc.intervalIntegrable 0 (T * (a - t_real))
            apply ContinuousAt.stronglyMeasurableAtFilter
            exact isOpen_univ
            intro x _
            exact Real.continuous_sinc.continuousAt
            exact mem_univ _
          · apply DifferentiableAt.mul
            · exact differentiableAt_const (T)
            · apply DifferentiableAt.sub
              · exact differentiableAt_id
              · exact differentiableAt_const (t_real)
    intro a
    exact (h_v_diff a).hasDerivAt
  have h_v_deriv_eq2 : ∀ a, HasDerivAt (Complex.ofReal ∘ v) (↑(deriv v a)) a := by
    intro a
    apply HasDerivAt.ofReal_comp
    exact h_v_deriv_eq a
  have h_IPP_Ici : ∫ (a : ℝ) in Ioi 0, u a * ↑(deriv v a) ∂volume =
  0 - (u 0 * ↑(v 0)) - ∫ (a : ℝ) in Ioi 0, deriv u a * ↑(v a) ∂volume := by
    apply MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a' := u 0 * ↑(v 0)) (b' := 0)
    · intro x hx
      exact (h_u_deriv_eq x)
    · intro x hx
      exact (h_v_deriv_eq2 x)
    · exact h_int_uv'.restrict
    · exact h_int_u'v.restrict
    · have h_cont_uv : ContinuousAt (fun x => u x * ↑(v x)) 0 :=
        ContinuousAt.mul (h_u_deriv_eq 0).continuousAt (h_v_deriv_eq2 0).continuousAt
      exact h_cont_uv.tendsto.mono_left nhdsWithin_le_nhds
    · exact h_uv_top

  unfold u v at h_IPP_Ici
  have: 0 - u 0 * ↑(v 0)=  - f 0 * cexp ( ↑↑t * ↑γ) * ↑(DirichletSin (-T *  ↑t)):= by
    unfold u v
    simp
  rw[this] at h_IPP_Ici

  unfold μ_real at *
  unfold non_negative_reals
  have h_Ioi_eq_Ici : ∫ (a : ℝ) in Ioi 0, u a * ↑(deriv v a) = ∫ (a : ℝ) in Ici 0, u a * ↑(deriv v a) := by
    have h_zero_null : volume ({0} : Set ℝ) = 0 := by
      exact measure_singleton 0
    have h_union : Ici (0:ℝ) = {0} ∪ Ioi 0 := by
      ext x
      rw [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi]
      rw [eq_comm]
      exact le_iff_eq_or_lt

    have h_split : ∫ (a : ℝ) in Ici 0, u a * ↑(deriv v a) =
    (∫ (a : ℝ) in {0}, u a * ↑(deriv v a)) + ∫ (a : ℝ) in Ioi 0, u a * ↑(deriv v a) := by
      simp_rw [h_union]
      have h_disj : Disjoint ({0} : Set ℝ) (Ioi 0) := by
        rw [Set.disjoint_singleton_left]
        unfold Ioi
        rw [Set.mem_setOf_eq]
        exact lt_irrefl 0
      exact MeasureTheory.setIntegral_union h_disj measurableSet_Ioi h_int_uv'.restrict h_int_uv'.restrict
    have h_meas_zero : volume ({0} : Set ℝ) = 0 := measure_singleton 0
    have h_int_zero : (∫ (a : ℝ) in {0}, u a * ↑(deriv v a)) = 0 := by
      apply MeasureTheory.setIntegral_measure_zero (fun a ↦  u a * ↑(deriv v a)) h_meas_zero

    rw[h_int_zero] at h_split
    simp at h_split
    rw[h_split]

  rw[h_Ioi_eq_Ici] at h_IPP_Ici

  have h_Ioi_eq_Ici2 : ∫ (a : ℝ) in Ioi 0, deriv (fun a ↦ f a * cexp (-(↑a - ↑↑t) * ↑γ)) a * ↑(DirichletSin (T * (a - ↑t))) = ∫ (a : ℝ) in Ici 0, deriv (fun a ↦ f a * cexp (-(↑a - ↑↑t) * ↑γ)) a * ↑(DirichletSin (T * (a - ↑t))) := by
    have h_zero_null : volume ({0} : Set ℝ) = 0 := by
      exact measure_singleton 0
    have h_union : Ici (0:ℝ) = {0} ∪ Ioi 0 := by
      ext x
      rw [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi]
      rw [eq_comm]
      exact le_iff_eq_or_lt

    have h_split : ∫ (a : ℝ) in Ici 0, deriv (fun a ↦ f a * cexp (-(↑a - ↑↑t) * ↑γ)) a * ↑(DirichletSin (T * (a - ↑t))) =
    (∫ (a : ℝ) in {0}, deriv (fun a ↦ f a * cexp (-(↑a - ↑↑t) * ↑γ)) a * ↑(DirichletSin (T * (a - ↑t)))) + ∫ (a : ℝ) in Ioi 0, deriv (fun a ↦ f a * cexp (-(↑a - ↑↑t) * ↑γ)) a * ↑(DirichletSin (T * (a - ↑t))) := by
      simp_rw [h_union]
      have h_disj : Disjoint ({0} : Set ℝ) (Ioi 0) := by
        rw [Set.disjoint_singleton_left]
        unfold Ioi
        rw [Set.mem_setOf_eq]
        exact lt_irrefl 0

      exact MeasureTheory.setIntegral_union h_disj measurableSet_Ioi h_int_u'v.restrict h_int_u'v.restrict
    have h_meas_zero : volume ({0} : Set ℝ) = 0 := measure_singleton 0
    have h_int_zero : (∫ (a : ℝ) in {0}, deriv (fun a ↦ f a * cexp (-(↑a - ↑↑t) * ↑γ)) a * ↑(DirichletSin (T * (a - ↑t)))) = 0 := by
      apply MeasureTheory.setIntegral_measure_zero (fun a ↦  deriv (fun a ↦ f a * cexp (-(↑a - ↑↑t) * ↑γ)) a * ↑(DirichletSin (T * (a - ↑t)))) h_meas_zero

    rw[h_int_zero] at h_split
    have: 0 + ∫ (a : ℝ) in Ioi 0, deriv (fun a ↦ f a * cexp (-(↑a - ↑↑t) * ↑γ)) a * ↑(DirichletSin (T * (a - ↑t)))= ∫ (a : ℝ) in Ioi 0, deriv (fun a ↦ f a * cexp (-(↑a - ↑↑t) * ↑γ)) a * ↑(DirichletSin (T * (a - ↑t))):= by
      simp
    rw[this] at h_split
    rw[h_split.symm]
  rw[h_Ioi_eq_Ici2] at h_IPP_Ici
  exact h_IPP_Ici


theorem Tendsto_Dirichlet_Integral (f : ℝ → ℂ) (γ: ℝ)(S: Set ℝ)(hS : ∀ x ∈ S, 0 < x)(t: S)
  (h_cont : Continuous f)
  (h_diff : Differentiable ℝ f)
  (h_int : Integrable (fun t ↦ f t * cexp (-γ * t)))
  (h_diff_int : Integrable (fun t ↦ (deriv f t) * cexp (-γ * t)))  :
  Tendsto (fun T : ℝ ↦ ∫ a, deriv (fun x ↦ f x * cexp (-((x - t) : ℝ) * γ)) a * ↑(DirichletSin (T * (a - t)))∂μ_real)
    atTop (𝓝 (-(f t))) := by
    rcases t with ⟨t_val, ht_mem⟩
    have ht_pos : 0 < t_val := hS t_val ht_mem
    have h_max : max 0 t_val = t_val := max_eq_right ht_pos.le
    simp only [Subtype.coe_mk]


    have hd_derivAt :  ∀ k:ℝ, HasDerivAt (fun k : ℝ ↦ cexp (-↑γ * ↑k)) (cexp (-↑γ * ↑k)*(-↑γ) ) k := by
          intro k
          apply HasDerivAt.cexp
          have h_id_coe : HasDerivAt (fun x : ℝ ↦ (↑x:ℂ )) 1 k := by
            exact HasDerivAt.ofReal_comp (hasDerivAt_id k)
          have h_coe_final:= h_id_coe.const_mul (-↑γ)
          have: -↑γ * (1:ℂ) = -↑γ:= by simp
          simp_rw[this] at h_coe_final
          exact h_coe_final

    let u := fun a : ℝ ↦ f a * cexp (-(a - t_val) * γ)
    have h_has_deriv_u : ∀ a:ℝ, HasDerivAt u (deriv f a * cexp (-(a - t_val) * γ) - f a * γ * cexp (-(a - t_val) * γ)) a := by
      have h_has_deriv_t_inS:= CExpDerivAt f γ S ⟨t_val, ht_mem⟩ h_diff
      unfold u
      simp only [Subtype.coe_mk] at h_has_deriv_t_inS
      exact h_has_deriv_t_inS


    have h_deriv_u_eq : ∀ a, deriv u a = deriv f a * cexp (-(a - t_val) * γ) - f a * γ * cexp (-(a - t_val) * γ) := by
      intro a
      exact (h_has_deriv_u a).deriv

    have h_int_u' : Integrable (fun a => deriv u a) := by
      simp_rw [h_deriv_u_eq]
      apply Integrable.sub
      · have h_int_shifted : Integrable (fun a ↦ (deriv f a * cexp (-(↑a - ↑t_val) * ↑γ))) := by
          have:(fun a ↦ (deriv f a * cexp (-(↑a - ↑t_val) * ↑γ))) = fun x ↦ deriv f x * cexp (- ↑γ* ↑x) * cexp (↑t_val * ↑γ) := by
            funext x
            ring_nf
            rw[Complex.exp_add]
            field_simp
          rw[this]
          apply Integrable.mul_const
          exact h_diff_int
        exact h_int_shifted
      · have h_int_f_shifted : Integrable (fun a ↦ (f a * ↑γ * cexp (-(↑a - ↑t_val) * ↑γ))) := by
          have:(fun a ↦ (f a * ↑γ* cexp (-(↑a - ↑t_val) * ↑γ))) = fun x ↦ ↑γ*f x * cexp (- ↑γ* ↑x) * cexp (↑t_val * ↑γ) := by
            funext x
            simp_rw [neg_sub]
            have: cexp ((↑t_val - ↑x) * ↑γ)= cexp (↑t_val* ↑γ - ↑x* ↑γ):= by
              ring_nf
            rw[this]
            rw[Complex.exp_sub]
            field_simp
            have: cexp (↑γ * ↑x) * cexp (-(↑γ * ↑x))=1 := by
              rw [← Complex.exp_add]
              ring_nf
              rw[Complex.exp_zero]
            by_cases h_f: f x =0
            simp[h_f]
            by_cases h_gamma: γ =0
            simp[h_gamma]
            field_simp[h_f,h_gamma]
            rw[this]
          rw[this]
          apply Integrable.mul_const
          have: (fun x ↦ ↑γ * f x * cexp (-↑γ * ↑x))= fun x ↦ ↑γ *( f x * cexp (-↑γ * ↑x)):= by
            funext x
            ring_nf
          rw[this]
          apply Integrable.const_mul (f:= fun x ↦ f x * cexp (-↑γ * ↑x)) (c:=↑γ)
          exact h_int
        exact h_int_f_shifted

    have: (fun a => deriv (fun x ↦ f x * cexp (-↑(x - ↑t_val) * ↑γ)) a)= fun a => deriv u a:= by
      funext a
      unfold u
      simp
    simp_rw[this]
    have h_u_dirichletInt:= Tendsto_Integral_DirichletSin_times_integrableFunction_zero' (fun a ↦ (deriv u) a) t_val h_int_u'
    simp at h_u_dirichletInt

    have h_lim_inf : Tendsto u atTop (𝓝 0) := by
      have h_eq : u  = fun a ↦ (f a * cexp (-↑γ * ↑a)) * cexp (↑γ * ↑t_val) := by
        funext a
        simp [u]

        have: f a * cexp (-(↑γ * ↑a)) * cexp (↑γ * ↑↑t_val)= f a * cexp (-(↑γ * ↑a)+↑γ * ↑↑t_val):= by
          by_cases h_f: f a =0
          simp[h_f]
          field_simp[h_f]
          rw [← Complex.exp_add]
          ring_nf
        simp_rw[this]
        ring_nf

      simp_rw [h_eq]
      have : (𝓝 (0:ℂ))= (𝓝 (0 * cexp (↑γ * ↑↑t_val))):= by
        simp
      rw[this]
      apply Tendsto.mul_const
      let g := fun k ↦ f k * cexp (-↑γ * ↑k)
      have h_g_diff_int : Integrable (deriv g) volume := by
        simp only [g]
        have h_deriv_eq : ∀ k, deriv g k = (deriv f k * cexp (-↑γ * ↑k)) + (f k * (-↑γ * cexp (-↑γ * ↑k))) := by
          intro k
          unfold g
          have hd : DifferentiableAt ℝ (fun k:ℝ ↦ cexp (-↑γ * ↑k)) k := by
            exact (hd_derivAt k).differentiableAt
          rw[ deriv_fun_mul (h_diff.differentiableAt) hd]
          rw [(hd_derivAt k).deriv]
          ring_nf
        rw [funext h_deriv_eq]
        apply Integrable.add
        · exact h_diff_int
        · have : (fun x ↦ f x * (-↑γ * cexp (-↑γ * ↑x)))= (fun x ↦ (-↑γ)* (f x *  cexp (-↑γ * ↑x))):= by
            funext x
            ring_nf
          rw[this]
          exact Integrable.const_mul h_int (-↑γ)
      unfold g at h_g_diff_int
      apply tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a:= 0)
      · intro x hx
        have h_deriv_eq : HasDerivAt (fun k ↦ f k * cexp (-↑γ * ↑k)) (deriv f x * cexp (-↑γ * ↑x) + f x * (-↑γ * cexp (-↑γ * ↑x))) x := by
          have:= (h_diff.differentiableAt).hasDerivAt.mul (hd_derivAt x)
          have h_rew : HasDerivAt (f * fun k:ℝ ↦ cexp (-↑γ * ↑k)) (deriv f x * cexp (-↑γ * ↑x) + f x * (-↑γ * cexp (-↑γ * ↑x))) x := by
            simpa [mul_comm] using this
          exact h_rew
        exact h_deriv_eq
      · have h_deriv_eq : ∀ x:ℝ, HasDerivAt (fun k ↦ f k * cexp (-↑γ * ↑k)) (deriv f x * cexp (-↑γ * ↑x) + f x * (-↑γ * cexp (-↑γ * ↑x))) x := by
          intro x
          have:= (h_diff.differentiableAt).hasDerivAt.mul (hd_derivAt x)
          have h_rew : HasDerivAt (f * fun k:ℝ ↦ cexp (-↑γ * ↑k)) (deriv f x * cexp (-↑γ * ↑x) + f x * (-↑γ * cexp (-↑γ * ↑x))) x := by
            simpa [mul_comm] using this
          exact h_rew
        have : (fun x ↦ deriv f x * cexp (-↑γ * ↑x) + f x * (-↑γ * cexp (-↑γ * ↑x))) = (fun x ↦ deriv (fun k ↦ f k * cexp (-↑γ * ↑k)) x) := by
          ext x
          rw [(h_deriv_eq x).deriv]
        rw [this]
        apply Integrable.integrableOn
        exact h_g_diff_int
      · apply Integrable.integrableOn
        exact h_int

    have h_integral_val : ∫ (a : ℝ) in Ioi ↑t_val, deriv u a = - u ↑t_val := by
      rw [show ( deriv u= fun x ↦ deriv f x * cexp (-(↑x - ↑↑t_val) * ↑γ) - f x * ↑γ * cexp (-(↑x - ↑↑t_val) * ↑γ)) from funext h_deriv_u_eq]
      rw [show ( deriv u= fun x ↦ deriv f x * cexp (-(↑x - ↑↑t_val) * ↑γ) - f x * ↑γ * cexp (-(↑x - ↑↑t_val) * ↑γ)) from funext h_deriv_u_eq] at h_int_u'

      have := integral_Ioi_of_hasDerivAt_of_tendsto ((h_has_deriv_u ↑t_val).continuousAt.continuousWithinAt) (fun x _hx ↦ h_has_deriv_u x) (h_int_u'.integrableOn) (h_lim_inf)
      simp at this
      simp
      exact this
    rw[h_max] at  h_u_dirichletInt
    rw[h_integral_val] at  h_u_dirichletInt
    have :  𝓝 (-u ↑t_val) =  𝓝 (-f ↑t_val):= by
      unfold u
      simp
    rw[this] at h_u_dirichletInt
    unfold μ_real
    unfold non_negative_reals
    have h_integral_eq : ∀ T, ∫ (a : ℝ) in Ici 0, deriv u a * ↑(DirichletSin (T * (a - t_val)))
                          = ∫ (a : ℝ) in Ioi 0, deriv u a * ↑(DirichletSin (T * (a - t_val))) := by
      intro T
      apply integral_Ici_eq_integral_Ioi
    simp_rw[h_integral_eq]
    exact h_u_dirichletInt

lemma Tendsto_Dirichlet_Integral_times_const(f : ℝ → ℂ) (γ: ℝ)(S: Set ℝ) (hS : ∀ x ∈ S, 0 < x)(t: S):
Tendsto (fun T : ℝ ↦ -f 0 * cexp (↑↑t * ↑γ) * ↑(DirichletSin (-T * ↑t))) atTop (𝓝 (0)):= by
  have ht_pos : 0 < (t : ℝ) := hS t t.prop
  have ht_neg : - (t : ℝ) < 0 := by linarith
  have h_lim_dirichlet : Tendsto (fun T ↦ DirichletSin (T * -(t : ℝ))) atTop (𝓝 (HeavisidePerso (-(t : ℝ)))) := by
    apply lim_S_Rx (-(t : ℝ))
  unfold HeavisidePerso at h_lim_dirichlet
  split_ifs at h_lim_dirichlet
  linarith [ht_neg]
  linarith [ht_neg]
  have h_complex : Tendsto (fun T ↦ (DirichletSin (T * -↑t) : ℂ)) atTop (𝓝 0) := by
    rw [← Complex.ofReal_zero]
    apply Tendsto.ofReal
    exact h_lim_dirichlet
  have:  (𝓝 (0:ℂ))=  (𝓝 (-f 0 * cexp (↑↑t * ↑γ) *0)):= by
    simp
  rw[this]
  apply Tendsto.const_mul
  have: (fun T ↦ (↑(DirichletSin (T * -t)):ℂ ))= fun T ↦ (↑(DirichletSin (-T * ↑t)):ℂ ):= by
    funext T
    simp

  simp_rw[this] at h_complex
  exact h_complex


theorem IsInverseLaplace (f : ℝ → ℂ) (γ : ℝ) (S : Set ℝ) (hS : ∀ x ∈ S, 0 < x)
    (h_cont : Continuous f)
    (h_int :Integrable (fun t ↦ f t * cexp (-(↑γ * ↑t))) volume)
    (hMeasurable : Measurable f)
    (h_Laplace_int : ∀ t ∈ S, Integrable ((InverseLaplaceKernelFunctT (RealLaplaceTransform f) t) γ) volume)
    (h_diff : Differentiable ℝ f)
    (h_diff_int : Integrable (fun t ↦ (deriv f t) * cexp (-γ * t))) :
    ∀ (t : S), (inverseLaplaceFunction (RealLaplaceTransform f) γ S h_Laplace_int) t = f t := by
  intro t
  have h_lim_LHS : Tendsto (fun T ↦ inverseLaplaceFunctionBounded (RealLaplaceTransform f) γ T S h_Laplace_int t)
      atTop (𝓝 ((inverseLaplaceFunction (RealLaplaceTransform f) γ S h_Laplace_int) t)) := by
    simp only [inverseLaplaceFunction, inverseLaplaceFunctionBounded, inverseLaplace_t, inverseLaplace_tBounded]
    apply Tendsto.const_mul
    apply Tendsto.congr'
    · filter_upwards [Filter.eventually_ge_atTop 0] with k hk
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    · apply Tendsto.congr'
      filter_upwards [Filter.eventually_ge_atTop 0] with k hk
      have hmink_le_k: -k≤k:= by
        linarith[hk]
      rw[← intervalIntegral.integral_of_le hmink_le_k]
      apply intervalIntegral_tendsto_integral
      exact h_Laplace_int t t.2
      exact tendsto_neg_atTop_atBot
      exact tendsto_id



  have h_lim_RHS : Tendsto (fun T ↦ inverseLaplaceFunctionBounded (RealLaplaceTransform f) γ T S h_Laplace_int t)
      atTop (𝓝 (f t)) := by
    apply Filter.Tendsto.congr'
    filter_upwards [Filter.eventually_ge_atTop 0] with T hT
    rw [IsInverseLaplaceBounded f γ T S h_cont h_int hMeasurable h_Laplace_int h_diff h_diff_int hT t]

    have: (fun t ↦ f t * cexp (-(↑γ * ↑t)))= fun t ↦ f t * cexp (-↑γ * ↑t):= by
      funext t
      ring_nf
    rw[this] at h_int
    apply Filter.Tendsto.congr'
    filter_upwards [Filter.eventually_ge_atTop 0] with T hT
    rw [ IsInverseLaplaceBounded' f γ T S h_cont h_diff h_int h_diff_int hT t]
    have : (𝓝 (f ↑t)) = (𝓝 (0-(- f ↑t))):= by
      simp
    rw[this]
    apply Tendsto.sub
    · exact Tendsto_Dirichlet_Integral_times_const f γ S hS t
    · have:= Tendsto_Dirichlet_Integral f γ S hS t h_cont h_diff h_int h_diff_int
      push_cast at this
      exact this


  apply tendsto_nhds_unique h_lim_LHS
  apply Filter.Tendsto.congr' _ h_lim_RHS
  filter_upwards [Filter.eventually_ge_atTop 0] with T hT
  rfl

end LaplaceInverse
section LaplaceTable

open Complex

/--
In this section, we will define tables of Laplace transform.
The table will consist of pairs LaplacePair :
1.a name of the function: no equality of functions is known apparently in Lean
2. the laplace transform
3. the values z for which the Laplace Transform converges
For now we will do the convergence check manually
-/
structure LaplacePair where
  name : String
  original_function : ℝ → ℂ
  laplace_transform : ℂ → ℂ
  convergence_set: Set ℂ




namespace LaplaceDB

open LaplacePair
open Complex

/--
define the Laplace Table
--/
abbrev Table := List LaplacePair
def UsualLaplaceTable : Table := []



/--
The next function is to update the table.
The function takes as entry:
1. the Laplace table
2. the function we want to add/update and its name
3. a convergence set
4. a proof that for all s∈E , the laplace transform is well defined.

--/

def update_laplace_table (table : Table) (f_name:String) (f : ℝ → ℂ) (E : Set ℂ)
    (h_integrable : ∀ s ∈ E, Integrable (RealFullLaplaceKernel f s) μ_c) :
    Table :=
    match table with
      |[] =>
        [{
      name := f_name,
      original_function := f,
      laplace_transform := RealLaplaceTransform f,
      convergence_set := E
        }]

      | p :: rest =>
        if p.name = f_name then
          {
        name := f_name,
        original_function := f,
        laplace_transform := RealLaplaceTransform f,
        convergence_set := p.convergence_set ∪ E
          } :: rest
        else
          p :: update_laplace_table rest f_name f E h_integrable

/--
Here we give a function version of the Laplace Transform
--/
def update_laplace_table_with_transform (table : Table)(f_name:String) (f : ℝ → ℂ) (g : ℂ → ℂ) (E : Set ℂ)
  (h_integrable : ∀ s ∈ E, Integrable (RealFullLaplaceKernel f s) μ_c)
  (h_g_is_transform: ∀ s ∈ E, RealLaplaceTransform f s = g s):
  Table :=
    match table with
      |[] =>
        [{
      name := f_name,
      original_function := f,
      laplace_transform := g,
      convergence_set := E
        }]

      | p :: rest =>
        if p.name = f_name then
          {
        name := f_name,
        original_function := f,
        laplace_transform := g,
        convergence_set := p.convergence_set ∪ E
          } :: rest
        else
          p :: (update_laplace_table_with_transform rest f_name f g E h_integrable h_g_is_transform)

/--
These functions look for a Laplace Pair and either output:
 the laplace pair
 the Laplace Transform
 the space of convergence
--/
def find_laplace_pair.LaplacePair(table : Table)(f_name:String):Option LaplacePair:=
  match table with
    |[] =>
      none
    | p :: rest =>
        if p.name = f_name then
          p
        else
         find_laplace_pair.LaplacePair rest f_name

def find_laplace_pair.LaplaceTrans(table : Table)(f_name:String):Option (ℂ → ℂ):=
  match table with
    |[] =>
      none
    | p :: rest =>
      if p.name = f_name then
        p.laplace_transform
      else
        find_laplace_pair.LaplaceTrans rest f_name

def find_laplace_pair.ConvSet(table : Table)(f_name:String):Option (Set ℂ):=
  match table with
    |[] =>
      none
    | p :: rest =>
      if p.name = f_name then
        p.convergence_set
      else
        find_laplace_pair.ConvSet rest f_name
