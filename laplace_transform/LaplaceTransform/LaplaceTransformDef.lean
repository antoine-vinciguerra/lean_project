import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory


import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Norm

import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.SpecialFunctions.Exponential
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
variable {V : Type*} [MeasureSpace V] [MeasurableSpace V]
variable {E : Type*} [NormedRing E] [CompleteSpace E] [NormedSpace ℂ E][NormedAlgebra ℂ E][MeasurableSpace E]
-- 𝕜 is a normed field which has an exponential defined,
-- E is a ℂ-normed vector space
section Defs
/-- the next function defines the kernel of the Laplace transform-/
def laplaceKernel (L : E → ℂ → E) (e : E) (s : ℂ) : E :=
  NormedSpace.exp ℂ (- (L e s))

-- The Laplace Transform of a function f: V → E with kernel defined by L.
def laplaceTransform (L : E → ℂ → E) (f :E → E) (μ : Measure E) (e : E) (s : ℂ) : E :=
  ∫ e, f e * (laplaceKernel L e s) • (1 : E) ∂μ

end Defs
