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

import Mathlib.Data.Complex.Basic




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
def μ_c : Measure  ℂ:= μ.map (↑)
-- The Laplace Transform of a function f: ℝ → ℂ.

def RealFullLaplaceKernel (f :ℝ → ℂ) (s : ℂ) : ℂ→ ℂ :=
  let f_tilde (z : ℂ) : ℂ :=
      if z.im = 0 then f z.re else 0
  fullLaplaceKernel L f_tilde s


def RealLaplaceTransform (f :ℝ → ℂ) : ℂ → ℂ  :=
  let f_tilde (z : ℂ) : ℂ :=
      if z.im = 0 then f z.re else 0
  GeneralizedLaplaceTransform L f_tilde μ_c

theorem RealLaplaceTransform_const_smul
   (f :ℝ → ℂ)  (r p : ℂ)
   (h_int : Integrable (RealFullLaplaceKernel f p ) μ_c) :
  RealLaplaceTransform  (r • f) p = r • RealLaplaceTransform f p := by
  unfold RealLaplaceTransform
  let f_tilde (z : ℂ) : ℂ :=
      if z.im = 0 then f z.re else 0
  have h_rf_tilde: (fun z ↦ if z.im = 0 then (r • f) z.re else 0)= r •f_tilde:= by
    simp_all only [Pi.smul_apply, smul_eq_mul, f_tilde]
    ext x : 1
    simp_all only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_zero]
  rw[h_rf_tilde]
  have h_integrable: Integrable (fullLaplaceKernel L f_tilde p) μ_c:= by
    simp_all only [Pi.smul_apply, smul_eq_mul, f_tilde]
    exact h_int
  apply GeneralizedLaplaceTransform_const_smul L f_tilde μ_c r p h_integrable
  apply (inferInstance : CompleteSpace ℂ)
  apply (inferInstance : IsBoundedSMul ℂ ℂ)



theorem RealLaplaceTransform_additive
   (f₁ : ℝ → ℂ)(f₂: ℝ → ℂ) (s : ℂ)
  (h_int₁ : Integrable (RealFullLaplaceKernel f₁ s))
  (h_int₂ : Integrable (RealFullLaplaceKernel f₂ s)):
  RealLaplaceTransform (f₁ + f₂) s =  RealLaplaceTransform f₁ s + RealLaplaceTransform f₂ s := by
  sorry

end Defs
