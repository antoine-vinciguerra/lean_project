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


import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Commute.Defs

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

theorem fullLaplaceKernel_complex_add
  (L : E → ℂ → E) (f : E → E)  (r s : ℂ)
   (h_L_linear : ∀ (e : E) (s₁ s₂ : ℂ),
   L e (s₁ + s₂) = L e s₁ + L e s₂)
   (h_E_commute :  ∀ (e₁ e₂ : E), Commute e₁ e₂):
    fullLaplaceKernel L f (r+s)= fullLaplaceKernel L (fullLaplaceKernel L f r) s:= by
    ext e
    calc
    (fullLaplaceKernel L f (r+s)) e
      = f e * (laplaceKernel L e (r+s) )• (1 : E):= by rw[fullLaplaceKernel]
    _=f e * (NormedSpace.exp ℂ (- (L e (r+s))) )• (1 : E) := by rw[laplaceKernel]
    _=f e * (NormedSpace.exp ℂ (- (L e r+ L e s)))• (1 : E):= by rw[h_L_linear]
    _=f e * (NormedSpace.exp ℂ (- L e r +(- L e s)))• (1 : E):= by rw [@neg_add]
    _=f e * (NormedSpace.exp ℂ (- L e r +(- L e s)))• (1 : E)• (1 : E):= by rw [one_smul]
    _=f e * (NormedSpace.exp ℂ (- L e r) * NormedSpace.exp ℂ (- L e s))• (1 : E)• (1 : E) := by
      have h_comm : Commute (-(L e r)) (-(L e s)) := by
        apply Commute.neg_left
        apply Commute.neg_right
        -- Since h_E_commute holds for ALL elements, it holds for L e r and L e s
        exact h_E_commute (L e r) (L e s)
      rw [NormedSpace.exp_add_of_commute h_comm]
    _=(f e * NormedSpace.exp ℂ (- L e r) )* NormedSpace.exp ℂ (- L e s)• (1 : E)• (1 : E) :=by
      simp_all only [smul_eq_mul, mul_one]
      rw [@NonUnitalRing.mul_assoc]
    _=((f e * NormedSpace.exp ℂ (- L e r) )• (1 : E))* NormedSpace.exp ℂ (- L e s)• (1 : E) := by
      simp only [smul_eq_mul, mul_one]
    _=((f e * laplaceKernel L e r)• (1 : E)) * (laplaceKernel L e s)• (1 : E):= by
        simp only [laplaceKernel]
    _=(f e * (laplaceKernel L e r)• (1 : E))* (laplaceKernel L e s)• (1 : E):= by
       simp only [smul_eq_mul, mul_one]
    _= ((fullLaplaceKernel L f r) e)* (laplaceKernel L e s)• (1 : E):= by
      rw[fullLaplaceKernel]
    _= (fullLaplaceKernel L (fullLaplaceKernel L f r) s) e:= by
      rw [←fullLaplaceKernel]



-- The Laplace Transform of a function f: V → E with kernel defined by L.
def GeneralizedLaplaceTransform (L : E → ℂ → E) (f :E → E) (μ : Measure E) : ℂ → E  :=
  fun s ↦ ∫ e, fullLaplaceKernel L f s e  ∂μ

theorem GeneralizedLaplaceTransform_const_smul
  {h_nr: NormedRing E} {h_c: CompleteSpace E}
  {h_na : NormedAlgebra ℂ E} {h_bounded: IsBoundedSMul ℂ E}
   (L : E → ℂ → E) (f : E → E) (μ : Measure E) (r s : ℂ)
  (h_int : Integrable (fullLaplaceKernel L f s ) μ) :
  GeneralizedLaplaceTransform L (r • f) μ s = r • GeneralizedLaplaceTransform L f μ s := by
  calc
  GeneralizedLaplaceTransform L (r • f) μ s
      = ∫ e, fullLaplaceKernel L (r • f) s e ∂μ := by rw [GeneralizedLaplaceTransform]
  _ = ∫ e, r • fullLaplaceKernel L f s e ∂μ := by
      -- factor r inside fullLaplaceKernel
      congr 1
      rw[fullLaplaceKernel_const_smul L f r s]
      simp_all only [Pi.smul_apply]
  _ = r • ∫ e, fullLaplaceKernel L f s e ∂μ := by
    rw[integral_smul r]
  _=  r • GeneralizedLaplaceTransform L f μ s := by rw [GeneralizedLaplaceTransform]


theorem GeneralizedLaplaceTransform_additive
  (L : E → ℂ → E) (f₁ : E → E)(f₂: E → E) (μ : Measure E) (s : ℂ)
  (h_int₁ : Integrable (fullLaplaceKernel L f₁ s ) μ)
  (h_int₂ : Integrable (fullLaplaceKernel L f₂ s ) μ):
  GeneralizedLaplaceTransform L (f₁ + f₂) μ s =  GeneralizedLaplaceTransform L f₁ μ s + laplaceTransform L f₂ μ s := by
  calc
  GeneralizedLaplaceTransform L (f₁ + f₂) μ s=∫ (e : E), fullLaplaceKernel L (f₁ + f₂) s e ∂μ:= by
    rw [GeneralizedLaplaceTransform]
  _=∫ (e : E),  ((f₁+f₂) e * (laplaceKernel L e s )• (1 : E)) ∂μ := by
    simp_rw [fullLaplaceKernel]
  _=∫ (e : E),  ((f₁ e +f₂ e) * (laplaceKernel L e s )• (1 : E)) ∂μ:= by
    simp_all only [Pi.add_apply,smul_eq_mul, mul_one]
  _= ∫ (e : E),  (f₁ e  * (laplaceKernel L e s )• (1 : E) +f₂ e * (laplaceKernel L e s )• (1 : E)) ∂μ:= by
    simp_rw [add_mul]
  _= ∫ (e : E),  (f₁ e  * (laplaceKernel L e s )• (1 : E))∂μ +∫ (e : E),(f₂ e * (laplaceKernel L e s )• (1 : E)) ∂μ:= by
    exact integral_add h_int₁ h_int₂
  _=∫ (e : E), fullLaplaceKernel L f₁ s e ∂μ + ∫ (e : E), fullLaplaceKernel L f₂ s e ∂μ:= by simp_rw[fullLaplaceKernel]
  _= GeneralizedLaplaceTransform L f₁ μ s + GeneralizedLaplaceTransform L f₂ μ s := by
    simp_rw [GeneralizedLaplaceTransform]

theorem GeneralizedLaplaceTransform_complex_add
  (L : E → ℂ → E) (f : E → E)(μ : Measure E) (s₁ s₂: ℂ)
  (h_L_linear : ∀ (e : E) (s₁ s₂ : ℂ),
   L e (s₁ + s₂) = L e s₁ + L e s₂)
  (h_int₁ : Integrable (fullLaplaceKernel L f s₁ ) μ)
  (h_int₂ : Integrable (fullLaplaceKernel L f (s₁+s₂) ) μ)
  (h_E_commute :  ∀ (e₁ e₂ : E), Commute e₁ e₂):
  GeneralizedLaplaceTransform L f μ (s₁+s₂) =  GeneralizedLaplaceTransform L (fullLaplaceKernel L f s₁) μ s₂ := by
  calc
  GeneralizedLaplaceTransform L f μ (s₁+s₂) =∫ (e : E), fullLaplaceKernel L f (s₁+s₂) e ∂μ:= by
    rw [GeneralizedLaplaceTransform]
  _=∫ (e : E),  fullLaplaceKernel L (fullLaplaceKernel L f s₁) s₂ e ∂μ := by
     congr 1
     ext e
     rw[←fullLaplaceKernel_complex_add L f s₁ s₂ h_L_linear h_E_commute]
  _= GeneralizedLaplaceTransform L (fullLaplaceKernel L f s₁) μ s₂ := by
    rw[GeneralizedLaplaceTransform]

end Defs
