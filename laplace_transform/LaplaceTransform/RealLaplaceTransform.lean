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
def L (z₁ z₂:ℂ ) :  ℂ:=
  z₁ * z₂
-- Define the set [0, ∞)
def non_negative_reals : Set ℝ := Ici 0

-- Define the measure on [0, ∞) as the Lebesgue measure restricted to that set
def μ : Measure ℝ := volume.restrict non_negative_reals

-- Now define the same for the right hand halfplane of the complex
def half_plane_pos_re : Set ℂ :=
  {z : ℂ | 0 < Complex.re z}

def μ_c: Measure ℂ := volume.restrict half_plane_pos_re
-- The Laplace Transform of a function f: ℝ → ℂ.

def RealFullLaplaceKernel (f :ℝ → ℂ) (s : ℂ) : ℂ→ ℂ :=
  let f_tilde (z : ℂ) : ℂ :=
    (Complex.exp ((-z.im)^2)) *f z.re / (Real.sqrt Real.pi)
  fullLaplaceKernel L f_tilde s


def RealLaplaceTransform (f :ℝ → ℂ) : ℂ → ℂ  :=
  let f_tilde (z : ℂ) : ℂ :=
    (Complex.exp ((-z.im)^2)) *f z.re / (Real.sqrt Real.pi)
  GeneralizedLaplaceTransform L f_tilde μ_c

theorem RealLaplaceTransform_const_smul
   (f :ℝ → ℂ)  (r p : ℂ)
   (h_int : Integrable (RealFullLaplaceKernel f p ) μ_c) :
  RealLaplaceTransform  (r • f) p = r • RealLaplaceTransform f p := by
  unfold RealLaplaceTransform
  let f_tilde (z : ℂ) : ℂ :=
    (Complex.exp ((-z.im)^2)) *f z.re / (Real.sqrt Real.pi)
  have h_rf_tilde:
  (fun z ↦ (Complex.exp ((-z.im)^2)) *( (r • f) z.re)
    / Real.sqrt Real.pi)= r •f_tilde:= by
      ext z
      simp[f_tilde]
      have h_rf_tilde_z:
      cexp (↑z.im ^ 2) * (r * f z.re) / ↑√Real.pi
      = r * (cexp (↑z.im ^ 2) * f z.re / ↑√Real.pi):= by calc
        cexp (↑z.im ^ 2) * (r * f z.re) / ↑√Real.pi=
        (cexp (↑z.im ^ 2) * r * f z.re) / ↑√Real.pi:= by rw [@NonUnitalRing.mul_assoc]
        _=(r* cexp (↑z.im ^ 2) * f z.re) / ↑√Real.pi:= by rw [mul_comm (cexp (↑z.im ^ 2)) r]
        _=r* (cexp (↑z.im ^ 2) * f z.re) / ↑√Real.pi:= by rw [@NonUnitalRing.mul_assoc]
        _=r * (cexp (↑z.im ^ 2) * f z.re / ↑√Real.pi):= by rw [@mul_div_assoc]
      rw[h_rf_tilde_z]
  rw[h_rf_tilde]
  have h_integrable: Integrable (fullLaplaceKernel L f_tilde p) μ_c:= by
    simp_all only [Pi.smul_apply, smul_eq_mul, f_tilde]
    exact h_int
  apply GeneralizedLaplaceTransform_const_smul L f_tilde μ_c r p h_integrable
  apply (inferInstance : CompleteSpace ℂ)
  apply (inferInstance : IsBoundedSMul ℂ ℂ)



theorem RealLaplaceTransform_additive
   (f₁ : ℝ → ℂ)(f₂: ℝ → ℂ) (p : ℂ)
  (h_int₁ : Integrable (RealFullLaplaceKernel f₁ p) μ_c)
  (h_int₂ : Integrable (RealFullLaplaceKernel f₂ p) μ_c):
  RealLaplaceTransform (f₁ + f₂) p =  RealLaplaceTransform f₁ p + RealLaplaceTransform f₂ p := by
  unfold RealLaplaceTransform
  let f_tilde₁ (z : ℂ) : ℂ :=
    (Complex.exp ((-z.im)^2)) *f₁ z.re / (Real.sqrt Real.pi)
  let f_tilde₂ (z : ℂ) : ℂ :=
    (Complex.exp ((-z.im)^2)) *f₂ z.re / (Real.sqrt Real.pi)

  have f_tilde_linear: (fun z ↦ cexp ((-↑z.im) ^ 2) * (f₁ + f₂) z.re / ↑√Real.pi)= f_tilde₁+ f_tilde₂:= by
    ext z
    simp[f_tilde₁, f_tilde₂]
    have  f_tilde_linear_z:
    cexp (↑z.im ^ 2) * (f₁ z.re + f₂ z.re) / ↑√Real.pi =
  cexp (↑z.im ^ 2) * f₁ z.re / ↑√Real.pi
  + cexp (↑z.im ^ 2) * f₂ z.re / ↑√Real.pi := by calc
    cexp (↑z.im ^ 2) * (f₁ z.re + f₂ z.re) / ↑√Real.pi=
    (cexp (↑z.im ^ 2) * (f₁ z.re + f₂ z.re)) / ↑√Real.pi:= by rw [div_ofReal]
      _= (cexp (↑z.im ^ 2) * f₁ z.re + cexp (↑z.im ^ 2) * f₂ z.re) / ↑√Real.pi:= by rw [@left_distrib]
      _= (cexp (↑z.im ^ 2) * f₁ z.re + cexp (↑z.im ^ 2) * f₂ z.re) *(1/ ↑√Real.pi):= by rw [@mul_one_div]
      _= (cexp (↑z.im ^ 2) * f₁ z.re )*(1/ ↑√Real.pi)+ ( cexp (↑z.im ^ 2) * f₂ z.re) *(1/ ↑√Real.pi):= by rw [@NonUnitalNonAssocRing.right_distrib]
      _= (cexp (↑z.im ^ 2) * f₁ z.re )/↑√Real.pi+  (cexp (↑z.im ^ 2) * f₂ z.re)*(1/ ↑√Real.pi):= by
        congr 1
        rw [@mul_one_div]
      _= (cexp (↑z.im ^ 2) * f₁ z.re )/↑√Real.pi+  (cexp (↑z.im ^ 2) * f₂ z.re)/↑√Real.pi:= by
        rw [@mul_one_div]
    rw[f_tilde_linear_z]
  rw[f_tilde_linear]
  have h_integrable₁: Integrable (fullLaplaceKernel L f_tilde₁ p) μ_c:= by
    simp_all only [Pi.add_apply, f_tilde₁, f_tilde₂]
    exact h_int₁
  have h_integrable₂: Integrable (fullLaplaceKernel L f_tilde₂ p) μ_c:= by
    simp_all only [Pi.add_apply, f_tilde₁, f_tilde₂]
    exact h_int₂
  apply GeneralizedLaplaceTransform_additive L f_tilde₁ f_tilde₂ μ_c p h_integrable₁ h_integrable₂

theorem RealLaplaceTransformIs
   (f: ℝ → ℂ) (p: ℂ):
  RealLaplaceTransform f p = ∫t, NormedSpace.exp ℂ (-p*t) * (f t) ∂μ  := by
  let all_R: set ℝ := ℝ
  let μ_2 : Measure ℝ × ℝ := volume.restrict (non_negative_reals × ℝ )
  unfold RealLaplaceTransform
  unfold L
  unfold GeneralizedLaplaceTransform
  unfold fullLaplaceKernel
  unfold laplaceKernel
  simp_all only [smul_eq_mul, mul_one, ite_mul, zero_mul, neg_mul]
  have equiv := Complex.measurableEquivRealProd
  have  equality_laplace:∫ (e : ℂ), cexp (-↑e.im ^ 2) * f e.re / ↑√Real.pi * NormedSpace.exp ℂ (-(e * p)) ∂μ_c =
  ∫ (t : ℝ), NormedSpace.exp ℂ (-(p * ↑t)) * f t ∂μ := by calc
    ∫ (e : ℂ), cexp (-↑e.im ^ 2) * f e.re / ↑√Real.pi * NormedSpace.exp ℂ (-(e * p)) ∂μ_c =
    ∫ (e: ( ℝ× ℝ)), cexp (-e.2 ^ 2) * f e.1 / ↑√Real.pi * NormedSpace.exp ℂ (-(e.1 * p)) ∂volume

def g (t : ℝ) : ℂ := 1

theorem iszero
  (s: ℂ): RealLaplaceTransform g s = 0 := by
  unfold RealLaplaceTransform
  unfold L
  unfold GeneralizedLaplaceTransform
  unfold fullLaplaceKernel
  unfold laplaceKernel
  unfold g
  simp_all only [smul_eq_mul, mul_one, ite_mul, zero_mul, neg_mul]
  simp_all only [one_mul]
  apply integral_eq_zero_of_ae
  rw [Filter.EventuallyEq, ae_iff]
  simp_all only [Pi.zero_apply, ite_eq_right_iff, Classical.not_imp]
  sorry


-- We show that that the definition of the laplace transform is as expected
def g_1 (t : ℝ) : ℂ := 1
def ExpectedLaplaceTransform (f : ℝ → ℂ) (p : ℂ) : ℂ := ∫t, NormedSpace.exp ℂ (-p*t) * (f t) ∂μ
theorem LaplaceTransformAppliedToOne
   (s: ℂ) (h: 0 < s.re): ExpectedLaplaceTransform g_1 s = 1/s := by
   unfold ExpectedLaplaceTransform
   calc ExpectedLaplaceTransform g_1 s
    = lim (atTop.map (fun T => ∫ t in Ioc 0 T, Complex.exp (-s * ↑t) * g_1 t ∂μ)) := by
    sorry


-- We now now apply prove the left-hand side of the table of Laplace transforms

-- We define the function f(x) = 1

def f (t : ℝ) : ℂ := 1
-- We apply the Laplace transform to f
theorem LaplaceTransformAppliedToOne
   (s: ℂ) (h: 0 < s.re): RealLaplaceTransform f s = 1/s := by
   unfold RealLaplaceTransform
   let f_tilde (z : ℂ) : ℂ :=
      if z.im = 0 then f z.re else 0
   calc GeneralizedLaplaceTransform L (fun z ↦ if z.im = 0 then f z.re else 0) μ_c s = ∫t, NormedSpace.exp ℂ (-s*(t : ℂ)) * (f_tilde t) ∂μ_c := by
    rw[GeneralizedLaplaceTransform]
  sorry

end Defs

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
