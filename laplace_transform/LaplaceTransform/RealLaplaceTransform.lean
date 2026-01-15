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
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.Analysis.Complex.Exponential

import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Filter.Basic
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
noncomputable def DirichletSin : ℝ → ℝ :=
  fun x↦ ∫ t in  (0).. (x), sinc t

noncomputable def HeavisidePerso (x : ℝ) : ℝ :=
  if x > 0 then 1 else if x = 0 then 1/2 else 0


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




theorem IsInverseLaplaceBounded  (f: ℝ → ℂ)(γ T: ℝ)(S: Set ℝ)
(h_cont : Continuous (f))
(h_int: Integrable (fun t ↦ (f t )*cexp (-(γ*t))))
(hMeasurable: Measurable f)
(h_Laplace_int: ∀ t∈ S, Integrable ((InverseLaplaceKernelFunctT (RealLaplaceTransform f) t) γ ) volume)
(h_diff : Differentiable ℝ f)
(h_diff_int: Integrable (fun t ↦ (deriv f t )*cexp (-γ*t)))
(hT : 0 ≤ T):
∀(t:S), (inverseLaplaceFunctionBounded (RealLaplaceTransform f) γ T S h_Laplace_int) t =  ∫ (a : ℝ), f a * cexp (-(↑a - ↑↑t) * ↑γ) *  ↑(Real.sin (T * (↑t - a))) / (↑π*(↑↑t - ↑a))  ∂μ_real:= by
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

  have h2ndIntegralCalc :
   ∫ (a : ℝ), I * cexp (↑γ * (↑↑t - ↑a)) * f a *
   ( ∫ (r : ℝ) in Icc (-T) T, cexp (I * ↑r * (↑↑t - ↑a)) )∂μ_real=
    ∫ (a : ℝ),I*cexp (↑γ * (↑↑t-↑a))*f a*
    ( 2 * Real.sin (T * (t - a)) / (t - a))∂μ_real := by
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

  simp_rw[h2ndIntegralCalc]

  rw[integrand_simplification t γ T f ]

theorem IsInverseLaplaceBounded' (f : ℝ → ℂ) (γ T : ℝ) (s : ℝ)
  (h_cont : Continuous f)
  (h_diff : Differentiable ℝ f)
  (h_int : Integrable (fun t ↦ f t * cexp (-γ * t)))
  (h_diff_int : Integrable (fun t ↦ (deriv f t) * cexp (-γ * t))) :
  ∫ t in Set.Ici 0, f t * cexp (-(t - s) * γ) * (Real.sin (T * (t - s)) / (π * (t - s))) =
  - f 0 * cexp (s * γ) * (DirichletSin (-T * s) / π) -
  ∫ t in Set.Ici 0, deriv (fun u ↦ f u * cexp (-(u - s) * γ)) t * (DirichletSin (T * (t - s)) / π) :=
sorry

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
