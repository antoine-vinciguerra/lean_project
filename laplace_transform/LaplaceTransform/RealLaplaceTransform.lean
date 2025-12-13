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

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Commute.Defs
import LaplaceTransform.LaplaceTransformDef
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.Analysis.Complex.Exponential

import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.Defs


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

def inverseLaplaceFunction (F : ℂ → ℂ) (γ: ℝ) (S: Set ℝ)
(h_integrable_in_S : ∀ t∈ S, Integrable ((InverseLaplaceKernelFunctT F t) γ ) volume)
 : S → ℂ :=
fun t↦ inverseLaplace_t F γ t

theorem inverseLaplaceAdditive_t(F₁: ℂ → ℂ) (F₂: ℂ → ℂ)(γ t : ℝ)
(h₁ :  Integrable (InverseLaplaceKernelFunctT F₁ t γ ) volume)
(h₂ : Integrable (InverseLaplaceKernelFunctT F₂ t γ ) volume): inverseLaplace_t (F₁+F₂) γ t = inverseLaplace_t F₁ γ t + inverseLaplace_t F₂ γ t:= by
  unfold inverseLaplace_t
  have h_const_ne_zero : (1 / (2 * I * ↑Real.pi) : ℂ) ≠ 0 := by
    simp_all only [one_div, mul_inv_rev, inv_I, neg_mul, mul_neg, ne_eq, neg_eq_zero, mul_eq_zero, inv_eq_zero,
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
