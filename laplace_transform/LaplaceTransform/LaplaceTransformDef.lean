import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.GroupWithZero.Action.Defs


import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Data.List.Defs
/-!


# The Generalized Version of the Laplace transform

-/

@[expose] public section


noncomputable section


open MeasureTheory Filter

open scoped Topology

/-! ## Most General version of Laplace transform -/

section Defs


variable {E : Type*} [NormedRing E] [CompleteSpace E]
[NormedSpace ℂ E][NormedAlgebra ℂ E][MeasurableSpace E]
[IsBoundedSMul ℂ E] [NormedSpace ℝ E] [SMulCommClass ℝ ℂ E]

-- E is a ℂ-normed vector space

/-- the next function defines the kernel of the Laplace transform-/
def laplaceKernel ( S : Set E) (L : S → ℂ → E) (e : S) (p : ℂ) : E :=
  NormedSpace.exp ℂ (- (L e p))

def fullLaplaceKernel ( S : Set E) (L : S → ℂ → E) (f :S → E) (p : ℂ) : S→ E :=
  fun e ↦ f e * (laplaceKernel S L e p )• (1 : E)


theorem fullLaplaceKernel_const_smul
  ( S : Set E) (L : S → ℂ → E) (f :S → E)  (r p : ℂ):
  fullLaplaceKernel S L (r • f) p   = r • fullLaplaceKernel S L  f p := by
    ext e
  -- Apply the definition of `fullLaplaceKernel` to the left-hand side (LHS)
    calc
    (fullLaplaceKernel S L (r • f) p) e
      = ((r • f) e) * (laplaceKernel S L e p) • (1 : E)    := by
          exact rfl
    _ = (r • (f e)) * (laplaceKernel S L e p) • (1 : E)    := by
          simp only [Pi.smul_apply]
    _ = r • ( (f e) * (laplaceKernel S L e p) • (1 : E) ) := by
          rw [smul_mul_assoc]
    _ = (r • fullLaplaceKernel S L f p) e                   := by
          simp only [fullLaplaceKernel, Pi.smul_apply]

theorem fullLaplaceKernel_complex_add
 ( S : Set E)(L : S → ℂ → E) (f : S→ E)  (r p : ℂ)
   (h_L_linear : ∀ (e : S) (p₁ p₂ : ℂ),
   L e (p₁ + p₂) = L e p₁ + L e p₂)
   (h_E_commute :  ∀ (e₁ e₂ : E), Commute e₁ e₂):
    fullLaplaceKernel S L f (r+p)= fullLaplaceKernel S L (fullLaplaceKernel S L f r) p:= by
    ext e
    calc
    (fullLaplaceKernel S L f (r+p)) e
      = f e * (laplaceKernel S L e (r+p) )• (1 : E):= by rw[fullLaplaceKernel]
    _=f e * (NormedSpace.exp ℂ (- (L e (r+p))) )• (1 : E) := by rw[laplaceKernel]
    _=f e * (NormedSpace.exp ℂ (- (L e r+ L e p)))• (1 : E):= by rw[h_L_linear]
    _=f e * (NormedSpace.exp ℂ (- L e r +(- L e p)))• (1 : E):= by rw [@neg_add]
    _=f e * (NormedSpace.exp ℂ (- L e r +(- L e p)))• (1 : E)• (1 : E):= by rw [one_smul]
    _=f e * (NormedSpace.exp ℂ (- L e r) * NormedSpace.exp ℂ (- L e p))• (1 : E)• (1 : E) := by
      have h_comm : Commute (-(L e r)) (-(L e p)) := by
        apply Commute.neg_left
        apply Commute.neg_right
        -- Since h_E_commute holds for ALL elements, it holds for L e r and L e s
        exact h_E_commute (L e r) (L e p)
      rw [NormedSpace.exp_add_of_commute h_comm]
    _=(f e * NormedSpace.exp ℂ (- L e r) )* NormedSpace.exp ℂ (- L e p)• (1 : E)• (1 : E) :=by
      simp_all only [smul_eq_mul, mul_one]
      rw [@NonUnitalRing.mul_assoc]
    _=((f e * NormedSpace.exp ℂ (- L e r) )• (1 : E))* NormedSpace.exp ℂ (- L e p)• (1 : E) := by
      simp only [smul_eq_mul, mul_one]
    _=((f e * laplaceKernel S L e r)• (1 : E)) * (laplaceKernel S L e p)• (1 : E):= by
        simp only [laplaceKernel]
    _=(f e * (laplaceKernel S L e r)• (1 : E))* (laplaceKernel S L e p)• (1 : E):= by
       simp only [smul_eq_mul, mul_one]
    _= ((fullLaplaceKernel S L f r) e)* (laplaceKernel S L e p)• (1 : E):= by
      rw[fullLaplaceKernel]
    _= (fullLaplaceKernel S L (fullLaplaceKernel S L f r) p) e:= by
      rw [←fullLaplaceKernel]



-- The Laplace Transform of a function f: V → E with kernel defined by L.
def GeneralizedLaplaceTransform( S : Set E) (L : S → ℂ → E) (f :S → E) (μ : Measure S) : ℂ → E  :=
  fun p ↦ ∫ e, fullLaplaceKernel S L f p e  ∂μ

theorem GeneralizedLaplaceTransform_const_smul
  {h_nr: NormedRing E} {h_c: CompleteSpace E}
  {h_na : NormedAlgebra ℂ E} {h_bounded: IsBoundedSMul ℂ E}
   ( S : Set E)(L : S → ℂ → E) (f : S → E) (μ : Measure S) (r p : ℂ)
  (h_int : Integrable (fullLaplaceKernel S L f p ) μ) :
  GeneralizedLaplaceTransform S L (r • f) μ p = r • GeneralizedLaplaceTransform S L f μ p := by
  calc
  GeneralizedLaplaceTransform S L (r • f) μ p
      = ∫ e, fullLaplaceKernel S L (r • f) p e ∂μ := by rw [GeneralizedLaplaceTransform]
  _ = ∫ e, r • fullLaplaceKernel S L f p e ∂μ := by
      -- factor r inside fullLaplaceKernel
      congr 1
      rw[fullLaplaceKernel_const_smul S L f r p]
      simp_all only [Pi.smul_apply]
  _ = r • ∫ e, fullLaplaceKernel S L f p e ∂μ := by
    rw[integral_smul r]
  _=  r • GeneralizedLaplaceTransform S L f μ p := by rw [GeneralizedLaplaceTransform]


theorem GeneralizedLaplaceTransform_additive
  ( S : Set E)(L : S → ℂ → E) (f₁ : S → E)(f₂: S → E) (μ : Measure S) (p : ℂ)
  (h_int₁ : Integrable (fullLaplaceKernel S L f₁ p ) μ)
  (h_int₂ : Integrable (fullLaplaceKernel S L f₂ p ) μ):
  GeneralizedLaplaceTransform S L (f₁ + f₂) μ p =  GeneralizedLaplaceTransform S L f₁ μ p + GeneralizedLaplaceTransform S L f₂ μ p := by
  calc
  GeneralizedLaplaceTransform S L (f₁ + f₂) μ p=∫ (e : S), fullLaplaceKernel S L (f₁ + f₂) p e ∂μ:= by
    rw [GeneralizedLaplaceTransform]
  _=∫ (e : S),  ((f₁+f₂) e * (laplaceKernel S L e p )• (1 : E)) ∂μ := by
    simp_rw [fullLaplaceKernel]
  _=∫ (e : S),  ((f₁ e +f₂ e) * (laplaceKernel S L e p )• (1 : E)) ∂μ:= by
    simp_all only [Pi.add_apply,smul_eq_mul, mul_one]
  _= ∫ (e : S),  (f₁ e  * (laplaceKernel S L e p )• (1 : E) +f₂ e * (laplaceKernel S L e p )• (1 : E)) ∂μ:= by
    simp_rw [add_mul]
  _= ∫ (e : S),  (f₁ e  * (laplaceKernel S L e p )• (1 : E))∂μ +∫ (e : S),(f₂ e * (laplaceKernel S L e p )• (1 : E)) ∂μ:= by
    exact integral_add h_int₁ h_int₂
  _=∫ (e : S), fullLaplaceKernel S L f₁ p e ∂μ + ∫ (e : S), fullLaplaceKernel S L f₂ p e ∂μ:= by simp_rw[fullLaplaceKernel]
  _= GeneralizedLaplaceTransform S L f₁ μ p + GeneralizedLaplaceTransform S L f₂ μ p := by
    simp_rw [GeneralizedLaplaceTransform]

theorem GeneralizedLaplaceTransform_complex_add
  ( S : Set E)(L : S → ℂ → E) (f : S → E)(μ : Measure S) (p₁ p₂: ℂ)
  (h_L_linear : ∀ (e : S) (p₁ p₂ : ℂ),
   L e (p₁ + p₂) = L e p₁ + L e p₂)
  (h_int₁ : Integrable (fullLaplaceKernel S L f p₁ ) μ)
  (h_int₂ : Integrable (fullLaplaceKernel S L f (p₁+p₂) ) μ)
  (h_E_commute :  ∀ (e₁ e₂ : E), Commute e₁ e₂):
  GeneralizedLaplaceTransform S L f μ (p₁+p₂) =  GeneralizedLaplaceTransform S L (fullLaplaceKernel S L f p₁) μ p₂ := by
  calc
  GeneralizedLaplaceTransform S L f μ (p₁+p₂) =∫ (e : S), fullLaplaceKernel S L f (p₁+p₂) e ∂μ:= by
    rw [GeneralizedLaplaceTransform]
  _=∫ (e : S),  fullLaplaceKernel S L (fullLaplaceKernel S L f p₁) p₂ e ∂μ := by
     congr 1
     ext e
     rw[←fullLaplaceKernel_complex_add S L f p₁ p₂ h_L_linear h_E_commute]
  _= GeneralizedLaplaceTransform S L (fullLaplaceKernel S L f p₁) μ p₂ := by
    rw[GeneralizedLaplaceTransform]

end Defs
