import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Norm

import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!


# The Laplace transform


## Design choices

## Main results
-/

@[expose] public section


noncomputable section


open MeasureTheory Filter

open scoped Topology

/-! ## Most General version of Laplace transform -/


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedRing E] [CompleteSpace E]
[NormedSpace ℂ E][NormedAlgebra ℂ E][MeasurableSpace E]
[IsBoundedSMul ℂ E] [NormedSpace ℝ E] [SMulCommClass ℝ ℂ E]

-- 𝕜 is a normed field which has an exponential defined,
-- E is a ℂ-normed vector space
section Defs
/-- the next function defines the kernel of the Laplace transform-/
def laplaceKernel (L : E → ℂ → E) (e : E) (s : ℂ) : E :=
  NormedSpace.exp ℂ (- (L e s))

def fullLaplaceKernel (L : E → ℂ → E) (f :E → E) (s : ℂ) : E→ E :=
  fun e ↦ f e * (laplaceKernel L e s )• (1 : E)


theorem fullLaplaceKernel_const_smul
  (L : E → ℂ → E) (f : E → E)  (r s : ℂ):
  fullLaplaceKernel L (r • f) s   = r • fullLaplaceKernel L  f s := by
    ext e
  -- Apply the definition of `fullLaplaceKernel` to the left-hand side (LHS)
    calc
    (fullLaplaceKernel L (r • f) s) e
      = ((r • f) e) * (laplaceKernel L e s) • (1 : E)    := by
          exact rfl
    _ = (r • (f e)) * (laplaceKernel L e s) • (1 : E)    := by
          simp only [Pi.smul_apply]
    _ = r • ( (f e) * (laplaceKernel L e s) • (1 : E) ) := by
          rw [smul_mul_assoc]
    _ = (r • fullLaplaceKernel L f s) e                   := by
          simp only [fullLaplaceKernel, Pi.smul_apply]


-- The Laplace Transform of a function f: V → E with kernel defined by L.
def laplaceTransform (L : E → ℂ → E) (f :E → E) (μ : Measure E) : ℂ → E  :=
  fun s ↦ ∫ e, fullLaplaceKernel L f s e  ∂μ

theorem LaplaceTransform_const_smul
  {h_nr: NormedRing E} {h_c: CompleteSpace E} {h_na : NormedAlgebra ℂ E} {h_bounded: IsBoundedSMul ℂ E} (L : E → ℂ → E) (f : E → E) (μ : Measure E) (r s : ℂ)
  (h_int : Integrable (fullLaplaceKernel L f s ) μ) :
  laplaceTransform L (r • f) μ s = r • laplaceTransform L f μ s := by
  calc
  laplaceTransform L (r • f) μ s
      = ∫ e, fullLaplaceKernel L (r • f) s e ∂μ := by rw [laplaceTransform]
  _ = ∫ e, r • fullLaplaceKernel L f s e ∂μ := by
      -- factor r inside fullLaplaceKernel
      congr 1
      rw[fullLaplaceKernel_const_smul L f r s]
      simp_all only [Pi.smul_apply]
  _ = r • ∫ e, fullLaplaceKernel L f s e ∂μ := by
    rw[integral_smul r]
  _=  r • laplaceTransform L f μ s := by rw [laplaceTransform]


theorem LaplaceTransform_additive
  (L : E → ℂ → E) (f₁ : E → E)(f₂: E → E) (μ : Measure E) (s : ℂ)
  (h_int₁ : Integrable (fullLaplaceKernel L f₁ s ) μ)
  (h_int₂ : Integrable (fullLaplaceKernel L f₂ s ) μ):
  laplaceTransform L (f₁ + f₂) μ s =  laplaceTransform L f₁ μ s + laplaceTransform L f₂ μ s := by
  calc
  laplaceTransform L (f₁ + f₂) μ s=∫ (e : E), fullLaplaceKernel L (f₁ + f₂) s e ∂μ:= by
    rw [laplaceTransform]
  _=∫ (e : E),  ((f₁+f₂) e * (laplaceKernel L e s )• (1 : E)) ∂μ := by
    simp_rw [fullLaplaceKernel]
  _=∫ (e : E),  ((f₁ e +f₂ e) * (laplaceKernel L e s )• (1 : E)) ∂μ:= by
    simp_all only [Pi.add_apply,smul_eq_mul, mul_one]
  _= ∫ (e : E),  (f₁ e  * (laplaceKernel L e s )• (1 : E) +f₂ e * (laplaceKernel L e s )• (1 : E)) ∂μ:= by
    simp_rw [add_mul]
  _= ∫ (e : E),  (f₁ e  * (laplaceKernel L e s )• (1 : E))∂μ +∫ (e : E),(f₂ e * (laplaceKernel L e s )• (1 : E)) ∂μ:= by
    exact integral_add h_int₁ h_int₂
  _=∫ (e : E), fullLaplaceKernel L f₁ s e ∂μ + ∫ (e : E), fullLaplaceKernel L f₂ s e ∂μ:= by simp_rw[fullLaplaceKernel]
  _= laplaceTransform L f₁ μ s + laplaceTransform L f₂ μ s := by
    simp_rw [laplaceTransform]

end Defs
