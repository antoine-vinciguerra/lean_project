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
   (f₁ : ℝ → ℂ)(f₂: ℝ → ℂ) (p : ℂ)
  (h_int₁ : Integrable (RealFullLaplaceKernel f₁ p) μ_c)
  (h_int₂ : Integrable (RealFullLaplaceKernel f₂ p) μ_c):
  RealLaplaceTransform (f₁ + f₂) p =  RealLaplaceTransform f₁ p + RealLaplaceTransform f₂ p := by
  unfold RealLaplaceTransform
  let f_tilde₁ (z : ℂ) : ℂ :=
      if z.im = 0 then f₁ z.re else 0
  let f_tilde₂ (z : ℂ) : ℂ :=
      if z.im = 0 then f₂ z.re else 0
  have f_tilde_linear: (fun z ↦ if z.im = 0 then (f₁ + f₂) z.re else 0)= f_tilde₁+ f_tilde₂:= by
    ext z
    simp only [Pi.add_apply]
    unfold f_tilde₁ f_tilde₂
    split
    next h => simp_all only
    next h => simp_all only [add_zero]
  rw[f_tilde_linear]
  have h_integrable₁: Integrable (fullLaplaceKernel L f_tilde₁ p) μ_c:= by
    simp_all only [Pi.add_apply, f_tilde₁, f_tilde₂]
    exact h_int₁
  have h_integrable₂: Integrable (fullLaplaceKernel L f_tilde₂ p) μ_c:= by
    simp_all only [Pi.add_apply, f_tilde₁, f_tilde₂]
    exact h_int₂
  apply GeneralizedLaplaceTransform_additive L f_tilde₁ f_tilde₂ μ_c p h_integrable₁ h_integrable₂

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
