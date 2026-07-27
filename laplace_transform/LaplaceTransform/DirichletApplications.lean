import LaplaceTransform.DirichletIntegral
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section


noncomputable section


open MeasureTheory Filter
open MeasureTheory Set
open MeasureTheory Complex Real Topology Filter
open scoped Topology
open scoped Pointwise
open Complex



/-
Applications of the limit of the Dirichlet integral
===================================================
-/


/-
SECTION 1 — Mathematical statement:

 DirichletSin(R * x)  ⟶  HeavisidePerso x       as R → +∞.
---------------------------------------------------------------


`DirichletSin` is the natural normalization of the primitive of `sinc`.

The constant `1/2` and the factor `1/π` are chosen precisely so that the limit is:
  * 1 on the right,
  * 0 on the left,
  * 1/2 at the jump point.

Thus it is an analytic approximation of the Heaviside function.
-/

noncomputable def DirichletSin : ℝ → ℝ :=
  fun x↦1/2 + 1/π * ∫ t in  (0).. (x), sinc t

noncomputable def HeavisidePerso (x : ℝ) : ℝ :=
  if x > 0 then 1 else if x = 0 then 1/2 else 0


lemma HeavisideNorm_le_one : ∀ a:ℝ, ‖HeavisidePerso  a‖ ≤ 1 := by
  unfold HeavisidePerso
  intro a
  split_ifs with h1 h2
  ·simp
  ·norm_num
  ·norm_num


theorem lim_S_Rx (x : ℝ) : Tendsto (fun R ↦ DirichletSin (R * x)) atTop (𝓝 (HeavisidePerso x)) := by
  unfold DirichletSin HeavisidePerso
  -- Split into three cases for x: x < 0, x = 0, and x > 0
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [hx, hx.ne, not_lt_of_lt hx]
    -- it suffices that the integral part tends to -π/2
    suffices Tendsto (fun R ↦ ∫ t in 0..R*x, sinc t) atTop (𝓝 (-π/2)) by
      convert (this.const_mul (1/π)).const_add (1/2) using 2
      ·field_simp
      · field_simp
        ring_nf

    -- Since x < 0 and R → ∞, the upper bound R*x → -∞.
    -- We use the change of variable t ↦ -t to transform this into the standard Dirichlet integral.
    have h_lim_pos : Tendsto (fun R ↦ - (R * x)) atTop atTop := tendsto_neg_atBot_atTop.comp (tendsto_id.atTop_mul_const_of_neg hx)
    convert (integral_dirichlet.comp h_lim_pos).neg using 1
    · ext R
      dsimp only [Function.comp_apply, neg_mul_eq_mul_neg]
      -- Use the property that sinc is an even function: sinc(-t) = sinc(t)
      rw [← neg_neg (R * x),show (0 : ℝ) = -0 by simp, ← intervalIntegral.integral_comp_neg (fun t ↦ sinc t), neg_zero]
      simp only [sinc_neg]
      rw [intervalIntegral.integral_symm, neg_neg (R * x)]
    · ring_nf
  · -- Case x = 0: DirichletSin(0) is defined as 1/2
    simp
  · -- Case x > 0: The limit is 1
    simp [hx]
    -- It suffices that the integral part tends to π/2.
    suffices Tendsto (fun R ↦ ∫ t in 0..R*x, sinc t) atTop (𝓝 (π/2)) by
      convert (this.const_mul (1/π)).const_add (1/2) using 2
      ·field_simp
      · field_simp
        ring_nf
    -- Since x > 0, R*x → ∞, so we simply compose the previously proven integral_dirichlet
    convert integral_dirichlet.comp (tendsto_id.atTop_mul_const hx) using 2


/-!
SECTION 2 — A global uniform bound for `DirichletSin`
----------------------------------

We know that:
  DirichletSin y → 1 as y → +∞,
  DirichletSin y → 0 as y → -∞.

Therefore the function is bounded on both tails.
On a central compact interval, it is bounded by continuity.

Conclusion: `DirichletSin` is bounded on the whole real line.

This global bound is essential for applying dominated convergence.
-/


--We first prove that `DirichletSin` is continuous, which is used to obtain a bound on a compact interval.

lemma DirichletSin_continuous : Continuous fun u ↦ DirichletSin (u):= by
  unfold DirichletSin
  apply Continuous.add
  · continuity
  · apply Continuous.mul
    · continuity
    · apply intervalIntegral.continuous_primitive
      apply Continuous.intervalIntegrable
      exact continuous_sinc



--The same continuity holds after composition with x ↦ T * (x - t).

lemma DirichletSin_continuous_comp (T:ℝ)(t:ℝ):Continuous fun x ↦ (DirichletSin (T * (x - t))):= by
  unfold DirichletSin
  push_cast
  apply Continuous.add
  · continuity
  · apply Continuous.mul
    · continuity
    · have : Continuous (fun x ↦ (∫ (t : ℝ) in 0..T * (x - ↑t), sinc t)):= by
        let F := fun (u : ℝ) ↦ ∫ (s : ℝ) in (0)..u, sinc s
        let g := fun (x : ℝ) ↦ T * (x - t)
        change Continuous (F ∘ g)
        apply Continuous.comp
        apply intervalIntegral.continuous_primitive
        apply Continuous.intervalIntegrable
        exact continuous_sinc
        unfold g
        apply Continuous.mul
        apply continuous_const
        apply Continuous.sub
        apply continuous_id
        apply continuous_const
      exact this


theorem DirichletSinBounded:  ∃ M, ∀ y, |DirichletSin y| ≤ M := by
  -- Step 1: Prove the function converges to 1 at +∞
  have h_lim_top : Tendsto DirichletSin atTop (𝓝 1) := by
    convert integral_dirichlet.const_mul (1/π) |>.const_add (1/2) using 1
    field_simp [Real.pi_ne_zero]; ring

  -- Step 2: Prove the function converges to 0 at -∞
  have h_lim_bot : Tendsto DirichletSin atBot (𝓝 0) := by
    let f_sym := fun u ↦ 1/2 + 1/π * (- ∫ t in 0..-u, sinc t)
    refine Tendsto.congr' (f₁ := f_sym) ?_ ?_
    · filter_upwards with u
      unfold DirichletSin f_sym
      rw [show (0 : ℝ) = -0 by simp, ← intervalIntegral.integral_comp_neg Real.sinc, show (-0 : ℝ) = 0 by simp]
      simp only [Real.sinc_neg, neg_zero]
      rw [intervalIntegral.integral_symm]
      ring_nf
    · convert (integral_dirichlet.comp tendsto_neg_atBot_atTop).neg.const_mul _ |>.const_add _ using 1
      field_simp [Real.pi_ne_zero]; ring

  -- Step 3: Use the limits to find bounds outside a large interval [-R, R]
    -- Since the limit at +∞ is 1, the function stays near 1 (and thus < 2) for large positive y
  have h_evt_top : ∀ᶠ y in atTop, ‖DirichletSin y‖ < 2 :=
    (h_lim_top.norm).eventually (eventually_lt_nhds (show ‖(1:ℝ)‖ < 2 by norm_num))
  obtain ⟨R_top, h_top⟩ := Filter.mem_atTop_sets.mp h_evt_top

  -- Since the limit at -∞ is 0, the function stays near 0 (and thus < 2) for large negative y
  have h_evt_bot : ∀ᶠ y in atBot, ‖DirichletSin y‖ < 2 :=
    (h_lim_bot.norm).eventually (eventually_lt_nhds (show ‖(0:ℝ)‖ < 2 by norm_num))
  obtain ⟨R_bot, h_bot⟩ := Filter.mem_atBot_sets.mp h_evt_bot

  -- Step 4: Bound the function on the central compact interval [-R, R]
  let R := max |R_top| |R_bot|
  -- A continuous function on a compact set is bounded (Extreme Value Theorem)
  obtain ⟨B, hB⟩ := (isCompact_Icc.image DirichletSin_continuous).isBounded.exists_norm_le

  -- Step 5: Combine the local bound (B) and the tail bound (2)
  use max B 2
  intro y
  rw [← Real.norm_eq_abs]
  by_cases hy : |y| ≤ R
  · -- Case |y| ≤ R: use the bound from the compact interval
    rw [abs_le] at hy
    exact le_trans (hB _ (mem_image_of_mem _ hy)) (le_max_left _ _)
  · -- Case |y| > R: use the bound from the limits at infinity
    rw [ not_le,lt_abs] at hy
    apply le_trans _ (le_max_right B 2)
    cases hy with
    | inl hy_pos =>
      have : y ≥ R_top := by
        apply le_trans _ (le_of_lt hy_pos)
        trans |R_top|; exact le_abs_self _; exact le_max_left _ _
      exact le_of_lt (h_top y this)
    | inr hy_neg =>
      have : y ≤ R_bot := by
        have hy_rev : y < -R := by linarith [hy_neg]
        apply le_trans (le_of_lt hy_rev)
        trans -|R_bot|; simp; exact le_max_right _ _; exact neg_abs_le R_bot
      exact le_of_lt (h_bot y this)


/-
The global bound remains true after composition with T * (x - t).
-/

theorem DirichletSinBoundedComp (T t : ℝ) (hT : T ≥ 0) : ∃ C : ℝ, ∀ x, |DirichletSin (T * (x - t))| ≤ C := by
  obtain ⟨M, hM⟩ := DirichletSinBounded
  use M
  intro x
  exact hM (T * (x - t))


/-
Uniform version: the same constant C bounds all the functions
x ↦ DirichletSin(T * (x - t)),
INDEPENDENTLY of T and x.
-/

lemma DirichletSinBoundedComp_forall (t : ℝ) :
    ∃ C : ℝ, ∀ T , ∀ x : ℝ, |DirichletSin (T * (x - t))| ≤ C := by --uniform with respect to T and t
  -- Use the previously proven global bound for DirichletSin
  obtain ⟨C, hC⟩ := DirichletSinBounded
  -- The bound C works for any input, including the composition T * (x - t)
  exact ⟨C, fun T x => hC (T * (x - t))⟩



/-!
SECTION 3 — Integrability of the product with the `DirichletSin` kernel
-------------------------------------------------------------
If f is integrable, then
  x ↦ f x * DirichletSin(T * (x - t))
is integrable.

Idea:
`DirichletSin(T * (x - t))` is measurable and bounded.
The product of an integrable function with a bounded measurable function is integrable.
-/

theorem Integrable_DirichletSin_times_integrableFunction (f:ℝ → ℝ ) (T t: ℝ ) (hT: T≥ 0) (hf: Integrable (fun t ↦ f t )): Integrable (fun x => f x * DirichletSin (T * (x - t))):= by
  obtain ⟨C, hC⟩ := DirichletSinBoundedComp T t hT
  have g_AESM: AEStronglyMeasurable (fun x ↦ DirichletSin (T * (x - t))) volume:= by
    apply Continuous.aestronglyMeasurable
    exact DirichletSin_continuous_comp T t
  have h_g_filter_bounded : ∀ᵐ (x : ℝ), ‖DirichletSin (T * (x - t))‖ ≤ C:= by
    filter_upwards
    simp_rw [Real.norm_eq_abs]
    exact hC
  apply MeasureTheory.Integrable.mul_bdd (f:= f) (g:=fun x => DirichletSin (T * (x - t)) ) (c:= C) hf g_AESM h_g_filter_bounded


/-
The same integrability lemma for a complex-valued function f.
-/

theorem Integrable_DirichletSin_times_integrableFunction' (f:ℝ → ℂ ) (T t: ℝ ) (hT: T≥ 0) (hf: Integrable (fun t ↦ f t )): Integrable (fun x => f x * ↑(DirichletSin (T * (x - t)))):= by
  obtain ⟨C, hC⟩ := DirichletSinBoundedComp T t hT
  have g_AESM: AEStronglyMeasurable (fun x ↦ (↑(DirichletSin (T * (x - t))) : ℂ)) volume:= by
    apply Continuous.aestronglyMeasurable
    have h_cont_re:=  (DirichletSin_continuous_comp T t)
    exact continuous_ofReal.comp h_cont_re
  have h_g_filter_bounded : ∀ᵐ (x : ℝ), ‖(↑(DirichletSin (T * (x - t))) : ℂ)‖ ≤ C:= by
    filter_upwards
    simp_rw[Complex.norm_real]
    simp_rw [Real.norm_eq_abs]
    exact hC
  apply MeasureTheory.Integrable.mul_bdd (f:= f) (g:=fun x => DirichletSin (T * (x - t)) ) (c:= C) hf g_AESM h_g_filter_bounded


/-!
SECTION 4 — Integral limit on a half-line
-----------------------------------------

As `T → ∞`, the integral `∫ a, f a * DirichletSin (T * (a - t))` converges
to the integral of `f` over `(t, +∞)`.

### Intuition
The pointwise limit of `DirichletSin (T * (a - t))` as `T → ∞` acts as:
  * 1   if a > t
  * 0   if a < t
  * 1/2 if a = t

Since `{t}` is Lebesgue-negligible, the integral limit isolates the domain `(t, +∞)`.
-/

theorem Tendsto_Integral_DirichletSin_times_integrableFunction (f : ℝ → ℝ) (t : ℝ) (hf : Integrable (fun t ↦ f t)) :
    Tendsto (fun T : ℝ ↦ ∫ a, f a * DirichletSin (T * (a - t)))
    atTop (𝓝 (∫ a in Ioi t, f a)) := by
  -- Step 1: Obtain a uniform bound C for the DirichletSin function
  rcases DirichletSinBoundedComp_forall t with ⟨C, hC⟩
  -- Rewrite the limit integral using an indicator function for the interval (t, ∞)
  rw [← integral_indicator measurableSet_Ioi]

  -- Step 2: Apply the Dominated Convergence Theorem (DCT)
  -- The dominating function is |f(a)| * |C|, which is integrable since f is integrable.
  apply tendsto_integral_filter_of_dominated_convergence (fun a ↦ |f a| * |C|)
  · -- Prove measurability of the integrand for sufficiently large T
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact (Integrable_DirichletSin_times_integrableFunction f T t hT hf).aestronglyMeasurable
  · -- Prove the domination condition: |f(a) * DirichletSin(T(a-t))| ≤ |f(a)| * |C|
    apply Filter.Eventually.of_forall
    intro T
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left ((hC T x).trans (le_abs_self C)) (abs_nonneg _)
  · -- Verify the integrability of the dominating function
    exact hf.abs.mul_const _
  · -- Step 4: Handle the pointwise convergence almost everywhere
    -- We exclude the single point a = t, which has measure zero.
    have h_neq : ∀ᵐ a, a ≠ t := by
      rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton];  exact measure_singleton t
    filter_upwards [h_neq] with a ha
    rw [Set.indicator_apply]
    -- Use the pointwise limit of DirichletSin, which is the HeavisidePerso function
    have h_lim : Tendsto (fun T ↦ DirichletSin (T * (a - t))) atTop (𝓝 (HeavisidePerso (a - t))) := lim_S_Rx (a - t)
    split_ifs with h_io
    · -- Case a > t: HeavisidePerso(a - t) = 1
      rw [HeavisidePerso, if_pos (sub_pos.mpr h_io)] at h_lim
      apply Tendsto.const_mul (f a) at h_lim
      rw [mul_one] at h_lim ; exact h_lim
    · -- Case a < t (since a ≠ t): HeavisidePerso(a - t) = 0
      simp only [mem_Ioi, not_lt] at h_io
      have ha_lt : a < t := lt_of_le_of_ne h_io ha
      have h_neg : a - t < 0 := sub_neg.mpr ha_lt
      rw [HeavisidePerso, if_neg h_neg.not_lt, if_neg h_neg.ne] at h_lim
      apply Tendsto.const_mul (f a) at h_lim
      rw [mul_zero] at h_lim; exact h_lim


/-!
SECTION 5 — Same application, complex-valued case
-------------------------------------------------
The same cutoff formula holds for an integrable complex-valued function.
-/

-- Same theorem, but now with a complex-valued function f : ℝ → ℂ.
theorem Tendsto_Integral_DirichletSin_times_integrableFunction' (f:ℝ → ℂ ) (t: ℝ ) (hf: Integrable (fun t ↦ f t )):
 Tendsto (fun T : ℝ ↦ ∫ a, f a * ↑(DirichletSin (T * (a - t))))
    atTop (𝓝 (∫ a in Ioi t, f a)):= by
  -- Step 1: Obtain a uniform bound C for the DirichletSin function
  rcases DirichletSinBoundedComp_forall t with ⟨C, hC⟩
  -- Rewrite the limit integral using an indicator function for the interval (t, ∞)
  rw [← integral_indicator measurableSet_Ioi]
  -- Step 2: Apply the Dominated Convergence Theorem (DCT)
  apply tendsto_integral_filter_of_dominated_convergence (fun a ↦ ‖f a‖* |C|)
  · -- Prove measurability of the integrand for sufficiently large T
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact (Integrable_DirichletSin_times_integrableFunction' f T t hT hf).aestronglyMeasurable
  · -- Prove the domination condition: ‖f(a) * DirichletSin(T(a-t))‖ ≤ ‖f(a)‖ * |C|
    apply Filter.Eventually.of_forall
    intro T
    apply Filter.Eventually.of_forall
    intro x
    rw [ norm_mul, Complex.norm_real]
    apply mul_le_mul_of_nonneg_left
    · exact (hC T x).trans (le_abs_self C)
    · exact norm_nonneg (f x)
  · -- Verify the integrability of the dominating function
    exact hf.norm.mul_const |C|
  · -- Step 3: Handle the pointwise convergence almost everywhere
    -- We exclude the single point a = t, which has measure zero.
    have h_neq : ∀ᵐ a, a ≠ t := by
      rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton];  exact measure_singleton t
    filter_upwards [h_neq] with a ha
    rw [Set.indicator_apply]
    -- Use the pointwise limit of DirichletSin, casted to ℂ
    have h_lim : Tendsto (fun T ↦ DirichletSin (T * (a - t))) atTop (𝓝 (HeavisidePerso (a - t))) := lim_S_Rx (a - t)
    split_ifs with h_io
    · -- Case a > t: HeavisidePerso(a - t) = 1
      rw [HeavisidePerso, if_pos (sub_pos.mpr h_io)] at h_lim
      have h_lim_2 : Tendsto (fun T ↦ (DirichletSin (T * (a - t)) : ℂ)) atTop (𝓝 (1 : ℂ)) :=by simpa using h_lim.ofReal
      apply Tendsto.const_mul (f a) at h_lim_2
      rw [mul_one] at h_lim_2 ; exact h_lim_2
    · -- Case a < t (since a ≠ t): HeavisidePerso(a - t) = 0
      simp only [mem_Ioi, not_lt] at h_io
      have ha_lt : a < t := lt_of_le_of_ne h_io ha
      have h_neg : a - t < 0 := sub_neg.mpr ha_lt
      rw [HeavisidePerso, if_neg h_neg.not_lt, if_neg h_neg.ne] at h_lim
      have h_lim_2 : Tendsto (fun T ↦ (DirichletSin (T * (a - t)) : ℂ)) atTop (𝓝 (0 : ℂ)) :=by simpa using h_lim.ofReal
      apply Tendsto.const_mul (f a) at h_lim_2
      rw [mul_zero] at h_lim_2; exact h_lim_2

/-!
SECTION 6 — Variant with the integral already restricted to (0, +∞)
-------------------------------------------------------------------

We now integrate only over `Ioi 0`.
-/

-- This time the integral is restricted to (0, ∞).
theorem Tendsto_Integral_DirichletSin_times_integrableFunction_zero' (f : ℝ → ℂ) (t : ℝ) (hf : Integrable (fun t ↦ f t)) :
    Tendsto (fun T : ℝ ↦ ∫ a in Ioi 0, f a * ↑(DirichletSin (T * (a - t))))
      atTop (𝓝 (∫ a in Ioi (max 0 t), f a)) := by
  -- Step 1: Handle the negligible singleton {t}
  have h_ae_neq : ∀ᵐ a, a ≠ t := by
    rw [ae_iff]
    have : {a | ¬a ≠ t} = {t} := by ext a ; simp
    rw [this]
    exact volume_singleton (a:=t)
  rcases DirichletSinBoundedComp_forall t with ⟨C, hC⟩
  -- Step 2: Use `convert` to apply DCT while changing the goal's limit expression
  convert tendsto_integral_filter_of_dominated_convergence (fun a ↦ ‖f a‖ * |C|) (f := fun a ↦ f a * ↑(HeavisidePerso (a - t))) (l := atTop) ?_ ?_ ?_ ?_ using 1
  · -- Step 3: Match the LHS and RHS integrals by comparing indicator domains
    congr 1
    symm
    rw [← integral_indicator measurableSet_Ioi]
    conv_rhs => rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    unfold HeavisidePerso
    filter_upwards [h_ae_neq] with a hat
    by_cases ha0 : a ∈ Ioi 0
    · -- Case: a > 0, check interaction with the cutoff at t
      rw [indicator_of_mem ha0]
      simp only [mem_Ioi] at ha0
      split_ifs with h_pos h_zero
      · simp only [sub_pos] at h_pos
        rw [indicator_of_mem];simp
        rwa [mem_Ioi, max_lt_iff, and_iff_right ha0]
      · exfalso
        exact hat (sub_eq_zero.mp h_zero)
      · rw [indicator_of_not_mem]; push_cast; rw[mul_zero]
        rw [mem_Ioi, max_lt_iff, not_and_or, not_lt]; right ;linarith
    · -- Case: a ≤ 0, the indicator on (0, ∞) vanishes
      rw [indicator_of_not_mem ha0, indicator_of_not_mem]
      rw [mem_Ioi, not_lt]
      rw[mem_Ioi] at ha0
      have h_ale0 : a ≤ 0 := by linarith [ha0]
      exact h_ale0.trans (le_max_left 0 t)
  · -- Verify filter is countably generated (trivial for atTop)
    exact instIsCountablyGenerated_atTop
  · -- Prove measurability of the restricted integrand
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact (Integrable_DirichletSin_times_integrableFunction' f T t hT hf).aestronglyMeasurable.restrict
  · -- Prove domination on the restricted domain
    filter_upwards with a
    filter_upwards with x
    rw [norm_mul]; rw [Complex.norm_real]
    refine mul_le_mul_of_nonneg_left ((hC _ _).trans (le_abs_self C)) (norm_nonneg _)
  · -- Verify integrability of the dominating function on the restriction
    exact hf.norm.mul_const |C| |>.restrict
  · -- Step 4: Pointwise convergence of the restricted kernel
    filter_upwards with a
    apply Tendsto.const_mul
    simpa using (lim_S_Rx (a - t)).ofReal

/-!
SECTION 7 — Scaled sinc integral on a half-line
-------------------------------------------------------------------

We now integrate only over `Ioi 0`.
-/
lemma integral_sinc_sq_scaled_of_pos (a : ℝ) (ha : 0 < a) :
    (∫ t in Ioi 0, (Real.sinc (a * t)) ^ 2) =
      (1 / a) * (Real.pi / 2) := by

  have hscale :=
    MeasureTheory.Measure.setIntegral_comp_smul_of_pos
      (volume : Measure ℝ)
      (fun u : ℝ => (Real.sinc u) ^ 2)
      (Ioi 0) ha
  have hzero: a • (Ioi (0 : ℝ)) = Ioi (0 : ℝ):= by
    ext x
    simp only [Set.mem_smul_set, Set.mem_Ioi, smul_eq_mul]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mul_pos ha hy
    · intro hx
      use (x / a)
      constructor
      · exact div_pos hx ha
      · exact mul_div_cancel₀ x (ne_of_gt ha)
  rw [hzero,
      Module.finrank_self,
      pow_one,
      integral_sinc_sq_eq_pi_div_two] at hscale
  simpa [smul_eq_mul, one_div] using hscale

lemma integral_sin_sq_div_sq_of_pos (a : ℝ) (ha : 0 < a) :
    (∫ t in Ioi 0, (Real.sin (a * t) / t) ^ 2) =
      Real.pi * a / 2 := by
  have h_ae :
      (fun t : ℝ => (Real.sin (a * t) / t) ^ 2)
        =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => a ^ 2 * (Real.sinc (a * t)) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hat0 : a * t ≠ 0 := mul_ne_zero ha.ne' ht0
    unfold Real.sinc
    rw [if_neg hat0]
    field_simp [ha.ne', ht0]
  rw [integral_congr_ae h_ae, integral_const_mul,
      integral_sinc_sq_scaled_of_pos a ha]
  field_simp [ha.ne']

/--
For every real parameter `a`,

`∫₀^∞ (sin (a t) / t)^2 dt = π |a| / 2`.
-/
theorem integral_sin_sq_div_sq (a : ℝ) :
    (∫ t in Ioi 0, (Real.sin (a * t) / t) ^ 2) =
      Real.pi * |a| / 2 := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have h := integral_sin_sq_div_sq_of_pos (-a) (neg_pos.mpr ha)
    calc
      (∫ t in Ioi 0, (Real.sin (a * t) / t) ^ 2)
          = ∫ t in Ioi 0, (Real.sin ((-a) * t) / t) ^ 2 := by
              apply integral_congr_ae
              filter_upwards with t
              rw [show a * t = -((-a) * t) by ring, Real.sin_neg]
              ring
      _ = Real.pi * (-a) / 2 := h
      _ = Real.pi * |a| / 2 := by
            rw [abs_of_neg ha]
  · simp
  · simpa [abs_of_pos ha] using
      integral_sin_sq_div_sq_of_pos a ha

/-!
SECTION 8 — sine and cosine integrals
-------------------------------------------------------------------
-/
/-- The quadratic sine kernel is integrable on `(0, ∞)`. -/
lemma integrableOn_sin_sq_div_sq (a : ℝ) :
    IntegrableOn
      (fun t : ℝ => (Real.sin (a * t) / t) ^ 2)
      (Ioi 0) := by
  by_cases ha : a = 0
  · subst a
    simp
  · apply Integrable.of_integral_ne_zero
    rw [integral_sin_sq_div_sq]
    have habs : 0 < |a| := abs_pos.mpr ha
    positivity

/--
For every real parameter `a`,

`∫₀^∞ (1 - cos (a t)) / t² dt = π |a| / 2`.

The proof uses `1 - cos x = 2 sin²(x/2)`.
-/
theorem integral_one_sub_cos_div_sq (a : ℝ) :
    (∫ t in Ioi 0, (1 - Real.cos (a * t)) / t ^ 2) =
      Real.pi * |a| / 2 := by
  have h_ae :
      (fun t : ℝ => (1 - Real.cos (a * t)) / t ^ 2)
        =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ =>
        2 * (Real.sin ((a / 2) * t) / t) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have h_trig : 1 - Real.cos (2 * (a / 2 * t)) = 2 * (Real.sin (a / 2 * t)) ^ 2 := by
      have h1 := Real.cos_sq_add_sin_sq (a / 2 * t)
      have h2 := Real.cos_two_mul (a / 2 * t)
      linarith
    rw [show a * t = 2 * ((a / 2) * t) by ring]
    rw[h_trig]
    field_simp [ht0]
  rw [integral_congr_ae h_ae, integral_const_mul,
      integral_sin_sq_div_sq (a / 2)]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring

/-- The cosine-difference kernel is integrable on `(0, ∞)`. -/
lemma integrableOn_one_sub_cos_div_sq (a : ℝ) :
    IntegrableOn
      (fun t : ℝ => (1 - Real.cos (a * t)) / t ^ 2)
      (Ioi 0) := by
  by_cases ha : a = 0
  · subst a
    simp
  · apply Integrable.of_integral_ne_zero
    rw [integral_one_sub_cos_div_sq]
    have habs : 0 < |a| := abs_pos.mpr ha
    positivity

/--
For nonnegative `a` and `b`,

`∫₀^∞ sin (a t) sin (b t) / t² dt = π min(a,b) / 2`.
-/
theorem integral_sin_mul_sin_div_sq
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ t in Ioi 0,
      Real.sin (a * t) * Real.sin (b * t) / t ^ 2) =
      Real.pi * min a b / 2 := by
  have h_ae :
      (fun t : ℝ =>
        Real.sin (a * t) * Real.sin (b * t) / t ^ 2)
        =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ =>
        (1 / 2 : ℝ) *
          (((1 - Real.cos ((a + b) * t)) / t ^ 2) -
           ((1 - Real.cos ((a - b) * t)) / t ^ 2))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    rw [show (a + b) * t = a * t + b * t by ring,
        show (a - b) * t = a * t - b * t by ring]
    have htrig := Real.two_mul_sin_mul_sin (a * t) (b * t)
    field_simp [ht0]
    simp
    have: Real.sin (a * t) * Real.sin (t * b) * 2= 2*Real.sin (a * t) * Real.sin (b * t):= by ring
    rw[this,htrig]
    field_simp
  rw [integral_congr_ae h_ae, integral_const_mul]
  rw [integral_sub
        (integrableOn_one_sub_cos_div_sq (a + b))
        (integrableOn_one_sub_cos_div_sq (a - b))]
  rw [integral_one_sub_cos_div_sq,
      integral_one_sub_cos_div_sq]
  rw [abs_of_nonneg (add_nonneg ha hb)]

  by_cases hab : a ≤ b
  · rw [abs_of_nonpos (sub_nonpos.mpr hab), min_eq_left hab]
    ring
  · have hba : b ≤ a := le_of_not_ge hab
    rw [abs_of_nonneg (sub_nonneg.mpr hba), min_eq_right hba]
    ring

/--
For positive `a` and `b`, the product of two scaled sinc functions
has integral

`∫₀^∞ sinc(a t) sinc(b t) dt = π / (2 max(a,b))`.
-/
theorem integral_sinc_mul_sinc
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi 0,
      Real.sinc (a * t) * Real.sinc (b * t)) =
      Real.pi / (2 * max a b) := by
  have h_ae :
      (fun t : ℝ =>
        Real.sinc (a * t) * Real.sinc (b * t))
        =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ =>
        (1 / (a * b)) *
          (Real.sin (a * t) * Real.sin (b * t) / t ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hat0 : a * t ≠ 0 := mul_ne_zero ha.ne' ht0
    have hbt0 : b * t ≠ 0 := mul_ne_zero hb.ne' ht0
    unfold Real.sinc
    rw [if_neg hat0, if_neg hbt0]
    field_simp [ha.ne', hb.ne', ht0]
  rw [integral_congr_ae h_ae, integral_const_mul,
      integral_sin_mul_sin_div_sq a b ha.le hb.le]
  by_cases hab : a ≤ b
  · rw [min_eq_left hab, max_eq_right hab]
    field_simp [ha.ne', hb.ne']
  · have hba : b ≤ a := le_of_not_ge hab
    rw [min_eq_right hba, max_eq_left hba]
    field_simp [ha.ne', hb.ne']

end

/-!
SECTION 9 — Lobachevsky's integral formula
-------------------------------------------------------------------
-/

/- We prove `∫₀^∞ (sinc x)^2 f(x)dx = ∫₀^π/2 f(x)dx`
    for a continuous function `π`-periodic function `f` satisfying
    the reflection symmetry  `f(π - x) = f(x)`.

The proof has three steps:

1. prove the identity for the Fourier modes `cos(2nx)`;
2. extend it by linearity to finite cosine polynomials;
3. approximate the original function uniformly by cosine polynomials and
   pass to the limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Real Topology
open scoped Topology BigOperators Interval

namespace Lobachevsky

def normalizedSincSquared : ℝ → ℝ := fun x ↦ (Real.sinc (Real.pi* x))  ^ 2

def cosinePolynomial
    (N : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    a n * Real.cos (2 * (n : ℝ) * x)


/--
A finite cosine polynomial with frequencies `0, 2, 4, ..., 2N`.

The frequency `2n` is chosen because `cos (2n(x + π)) = cos (2nx)`;
therefore every such polynomial is `π`-periodic.
-/
lemma continuous_cosinePolynomial
    (N : ℕ) (a : ℕ → ℝ) :
    Continuous (cosinePolynomial N a) := by
  apply continuous_finset_sum
  intro n hn
  apply Continuous.mul
  · exact continuous_const
  · continuity

lemma periodic_cosinePolynomial
    (N : ℕ) (a : ℕ → ℝ) :
    Function.Periodic
      (cosinePolynomial N a)
      Real.pi := by
    intro x
    simp only [cosinePolynomial, Finset.sum_congr rfl]
    congr
    ext n
    have h_arg : 2 * (n : ℝ) * (x + Real.pi) = 2 * (n : ℝ) * x + (2 * (n : ℝ)) * Real.pi := by ring
    rw [h_arg]
    simp only [Real.cos_add]
    have h_mul : 2 * (n : ℝ) * Real.pi = ((2 * n : ℕ) : ℝ) * Real.pi := by norm_cast
    rw[h_mul]
    rw[Real.sin_nat_mul_pi (2 * n), Real.cos_nat_mul_pi (2 * n)]
    ring
    have : n * 2 = 2 * n := by ring
    rw [this]
    rw [pow_mul, neg_one_sq]
    ring

lemma periodic_nat_mul_pi
  (hf_periodic : Function.Periodic f Real.pi)
  (n : ℕ) (x : ℝ) :
  f ((n : ℝ) * Real.pi + x) = f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
    f (↑(n + 1) * π + x) = f ((n : ℝ) * Real.pi + Real.pi + x) := by simp; ring
    _= f ((n : ℝ) * Real.pi + x):= by
      rw [show (n : ℝ) * Real.pi + Real.pi + x = ((n : ℝ) * Real.pi + x) + Real.pi by ring]
      exact hf_periodic _
    _= f x := by
      rw [ih]

lemma periodic_int_mul_pi
    (hf_periodic : Function.Periodic f Real.pi)
    (n : ℤ) (x : ℝ) :
    f (x + (n : ℝ) * Real.pi) = f x := by
  cases n with
  | ofNat k =>
    calc
      f (x + (k : ℝ) * Real.pi) = f ((k : ℝ) * Real.pi + x) := by rw [add_comm]
      _ = f x := periodic_nat_mul_pi hf_periodic k x
  | negSucc k =>
      have h := periodic_nat_mul_pi hf_periodic (k + 1) (x - ((k + 1 : ℕ) : ℝ) * Real.pi)
      have h_simp : ((k + 1 : ℕ) : ℝ) * Real.pi + (x - ((k + 1 : ℕ) : ℝ) * Real.pi) = x := by ring
      rw [h_simp] at h
      calc
      f (x + (Int.negSucc k : ℝ) * Real.pi)
        = f (x - ((k + 1 : ℕ) : ℝ) * Real.pi) := by
        congr 1
        push_cast
        ring
      _ = f x := h.symm

lemma exists_mod_pi_mem_Ico (x : ℝ) :
    ∃ n : ℤ,
      x - (n : ℝ) * Real.pi ∈ Set.Ico (0 : ℝ) Real.pi := by
  let n := Int.floor (x / Real.pi)
  use n
  constructor
  · have h1 : (n : ℝ) * Real.pi ≤ x := by
      have h2 : (n : ℝ) ≤ x / Real.pi := by
        exact Int.floor_le (x / Real.pi)
      have h3 : (n : ℝ) * Real.pi ≤ x := (le_div_iff₀ Real.pi_pos).mp h2
      linarith [h3]
    linarith
  · have h1 : x < (n + 1 : ℝ) * Real.pi := by
      have h2 : x / Real.pi < (n + 1 : ℝ) := by
        exact Int.lt_floor_add_one (x / Real.pi)
      have h3 : x < (n + 1 : ℝ) * Real.pi := (div_lt_iff₀ Real.pi_pos).mp h2
      linarith [h3]
    linarith

/--
A continuous `π`-periodic real function is bounded on the whole real line.
-/
lemma bounded_of_continuous_periodic_pi
    (hf_cont : Continuous f)
    (hf_periodic : Function.Periodic f Real.pi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |f x| ≤ C := by
  have h_Icc_nonempty : (Set.Icc (0 : ℝ) Real.pi).Nonempty := by
    use 0
    simp [Real.pi_nonneg]
  have h_comp : IsCompact (Set.Icc (0 : ℝ) Real.pi) := isCompact_Icc
  obtain ⟨x_max, hx_mem, hx_max⟩ :=
    IsCompact.exists_isMaxOn h_comp h_Icc_nonempty hf_cont.abs.continuousOn
  use |f x_max|
  constructor
  · exact abs_nonneg (f x_max)
  · intro x
    obtain ⟨n, hn⟩ := exists_mod_pi_mem_Ico x

    have h_eq : f x = f (x - (n : ℝ) * Real.pi) := by
      have h:= periodic_int_mul_pi hf_periodic n (x - (n : ℝ) * Real.pi)
      simp at h
      exact h
    rw [h_eq]
    have h_mem : x - (n : ℝ) * Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := Set.Ico_subset_Icc_self hn
    exact hx_max h_mem

lemma even_cosinePolynomial
    (N : ℕ) (a : ℕ → ℝ) :
    ∀ x : ℝ,
      cosinePolynomial N a (-x) =
        cosinePolynomial N a x := by
  intro x
  simp [cosinePolynomial]

/--
Multiplying `sinc²` by a continuous bounded function preserves
integrability on `(0, ∞)`.
-/
lemma integrableOn_sinc_sq_mul
    (hf_cont : Continuous f)
    (hf_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |f x| ≤ C) :
    IntegrableOn
      (fun x : ℝ => (Real.sinc x) ^ 2 * f x)
      (Set.Ioi 0) := by
  obtain ⟨C, _, hC_bound⟩ := hf_bounded
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)) :=
    hf_cont.aestronglyMeasurable.restrict
  have hf_bound_ae : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), ‖f x‖ ≤ C := by
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs]
    exact hC_bound x
  exact MeasureTheory.Integrable.mul_bdd integrable_sinc_sq hf_meas hf_bound_ae

/--
The product of `sinc²` with one cosine Fourier mode is integrable.
-/
lemma integrableOn_sinc_sq_mul_cos_two_nat (n : ℕ) :
    IntegrableOn
      (fun x : ℝ =>
        (Real.sinc x) ^ 2 *
          Real.cos (2 * (n : ℝ) * x))
      (Set.Ioi 0) := by
  have hf_cont : Continuous (fun x : ℝ => Real.cos (2 * (n : ℝ) * x)) := by
    continuity
  have hf_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |(fun y : ℝ => Real.cos (2 * (n : ℝ) * y)) x| ≤ C:= by
    use 1
    constructor
    · norm_num
    · intro x
      simp only [Real.abs_cos_le_one]
  exact integrableOn_sinc_sq_mul hf_cont hf_bounded

lemma sinc_sq_mul_cos_two_nat_ae (n : ℕ) :
    (fun x : ℝ =>
      (Real.sinc x) ^ 2 *
        Real.cos (2 * (n : ℝ) * x))
      =ᵐ[volume.restrict (Set.Ioi 0)]
    (fun x : ℝ =>
      (1 / 4 : ℝ) *
        (((1 - Real.cos (2 * ((n : ℝ) + 1) * x)) / x ^ 2) +
         ((1 - Real.cos (2 * ((n : ℝ) - 1) * x)) / x ^ 2) -
         2 *
           ((1 - Real.cos (2 * (n : ℝ) * x)) / x ^ 2))) := by
  filter_upwards [ae_restrict_mem (measurableSet_Ioi)]
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold Real.sinc
  rw [if_neg hx0]
  have h_cos_plus : Real.cos (2 * ((n : ℝ) + 1) * x) = Real.cos (2 * (n : ℝ) * x) * Real.cos (2 * x) - Real.sin (2 * (n : ℝ) * x) * Real.sin (2 * x) := by
    have : 2 * ((n : ℝ) + 1) * x = 2 * (n : ℝ) * x + 2 * x := by ring
    rw [this, Real.cos_add]
  have h_cos_minus : Real.cos (2 * ((n : ℝ) - 1) * x) = Real.cos (2 * (n : ℝ) * x) * Real.cos (2 * x) + Real.sin (2 * (n : ℝ) * x) * Real.sin (2 * x) := by
    have : 2 * ((n : ℝ) - 1) * x = 2 * (n : ℝ) * x - 2 * x := by ring
    rw [this, Real.cos_sub]
  rw [h_cos_plus,h_cos_minus]
  have h_cos_double : Real.cos (2 * x) = 1 - 2 * (Real.sin x)^2 := by
    calc Real.cos (2 * x)
      _ = 2*Real.cos x ^ 2 - 1 := Real.cos_two_mul x
      _ = (1 - Real.sin x ^ 2) - Real.sin x ^ 2 := by rw [← Real.sin_sq_add_cos_sq x]; ring
      _ = 1 - 2 * Real.sin x ^ 2 := by ring
  rw [h_cos_double]
  ring

/--
All nonconstant cosine modes are annihilated by integration against
`sinc²` on `(0, ∞)`.

The previous decomposition reduces the calculation to three known
integrals. Their values cancel exactly when `n > 0`.
-/

lemma integral_sinc_sq_mul_cos_two_nat
    (n : ℕ) (hn : 0 < n) :
    (∫ x in Set.Ioi 0,
      (Real.sinc x) ^ 2 *
        Real.cos (2 * (n : ℝ) * x)) = 0 := by
    have h_eq_int : (∫ x in Set.Ioi 0, (Real.sinc x) ^ 2 * Real.cos (2 * (n : ℝ) * x)) =
      ∫ x in Set.Ioi 0, (1 / 4 : ℝ) *
        (((1 - Real.cos (2 * ((n : ℝ) + 1) * x)) / x ^ 2) +
         ((1 - Real.cos (2 * ((n : ℝ) - 1) * x)) / x ^ 2) -
         2 * ((1 - Real.cos (2 * (n : ℝ) * x)) / x ^ 2)) := by
      apply integral_congr_ae
      exact sinc_sq_mul_cos_two_nat_ae n
    rw [h_eq_int, integral_const_mul]
    have h_int_piece1 : IntegrableOn (fun x : ℝ => (1 - Real.cos (2 * ((n : ℝ) + 1) * x)) / x ^ 2) (Set.Ioi 0) := by
      apply integrableOn_one_sub_cos_div_sq
    have h_int_piece2 : IntegrableOn (fun x : ℝ => (1 - Real.cos (2 * ((n : ℝ) - 1) * x)) / x ^ 2) (Set.Ioi 0) := by
      apply integrableOn_one_sub_cos_div_sq
    have h_int_piece3: IntegrableOn (fun x : ℝ =>   (1 - Real.cos (2 * (n : ℝ) * x)) / x ^ 2) (Set.Ioi 0) := by
      apply integrableOn_one_sub_cos_div_sq
    have h_int_piece3Tot:= h_int_piece3.const_mul 2
    have h_int_piece12 :Integrable
      (fun x : ℝ =>
        (1 - Real.cos (2 * ((n : ℝ) + 1) * x)) / x ^ 2 +
        (1 - Real.cos (2 * ((n : ℝ) - 1) * x)) / x ^ 2)
      (volume.restrict (Set.Ioi 0)) := h_int_piece1.add h_int_piece2
    rw [integral_sub h_int_piece12 h_int_piece3Tot]
    rw [integral_add h_int_piece1 h_int_piece2]
    rw [integral_const_mul]
    rw [integral_one_sub_cos_div_sq
      (2 * ((n : ℝ) + 1))]
    rw [integral_one_sub_cos_div_sq
      (2 * ((n : ℝ) - 1))]
    rw [integral_one_sub_cos_div_sq
      (2 * (n : ℝ))]
    field_simp [hn.ne, mul_assoc, mul_comm 2, mul_comm 4]
    simp
    have hn1_nat : 1 ≤ n := by omega
    have hn1_real : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn1_nat
    rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
    rw [abs_of_nonneg (sub_nonneg.mpr hn1_real)]
    ring

lemma intervalIntegral_cos_two_nat
    (n : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..Real.pi / 2,
      Real.cos (2 * (n : ℝ) * x)) = 0 := by
  let c : ℝ := 2 * (n : ℝ)
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  change (∫ x in (0 : ℝ)..Real.pi / 2,
      Real.cos (c * x)) = 0
  have hint :
    ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
        HasDerivAt
        (fun y : ℝ => Real.sin (c * y) / c)
        (Real.cos (c * x))
        x := by
    intro x _
    convert
    (((hasDerivAt_id x).const_mul c).sin.div_const c)
    using 1
    field_simp [hc]
    simp
  have hintegrable :
      IntervalIntegrable
        (fun x : ℝ => Real.cos (c * x))
        volume 0 (Real.pi / 2) := by
    exact
      (by
        fun_prop :
        Continuous (fun x : ℝ => Real.cos (c * x))
      ).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hint hintegrable]
  have harg :
      c * (Real.pi / 2) = (n : ℝ) * Real.pi := by
    dsimp [c]
    ring
  rw [harg, Real.sin_nat_mul_pi]
  simp

lemma intervalIntegral_one_zero_pi_div_two :
    (∫ x in (0 : ℝ)..Real.pi / 2, (1 : ℝ)) =
      Real.pi / 2 := by
  have h_integrable : IntervalIntegrable (fun x : ℝ => (1 : ℝ)) volume 0 (Real.pi / 2) := by
    exact (continuous_const.intervalIntegrable 0 (Real.pi / 2))
  have hint :
    ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
        HasDerivAt
        (fun y : ℝ => y)
        (1)
        x := by
    intro x _
    exact hasDerivAt_id' x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hint h_integrable]
  simp

/--
The product of `sinc²` with any finite cosine polynomial is integrable.

This is an immediate application of continuity, periodic boundedness, and
the general bounded-multiplier lemma above.
-/
lemma integrableOn_sinc_sq_mul_cosinePolynomial
    (N : ℕ) (a : ℕ → ℝ) :
    IntegrableOn
      (fun x : ℝ =>
        (Real.sinc x) ^ 2 *
          cosinePolynomial N a x)
      (Set.Ioi 0) := by
  apply integrableOn_sinc_sq_mul
  · exact continuous_cosinePolynomial N a
  · exact bounded_of_continuous_periodic_pi
      (continuous_cosinePolynomial N a)
      (periodic_cosinePolynomial N a)

/--
Lobachevsky's formula holds for every finite cosine polynomial.
-/
lemma lobachevsky_cosinePolynomial
    (N : ℕ) (a : ℕ → ℝ) :
    (∫ x in Set.Ioi 0,
      (Real.sinc x) ^ 2 *
        cosinePolynomial N a x)
      =
    ∫ x in (0 : ℝ)..Real.pi / 2,
      cosinePolynomial N a x := by
  classical

  -- First prove the formula separately for each cosine mode
  -- `x ↦ cos (2 n x)`.
  have hmode (n : ℕ) :
      (∫ x in Set.Ioi 0,
        (Real.sinc x) ^ 2 *
          Real.cos (2 * (n : ℝ) * x))
        =
      ∫ x in (0 : ℝ)..Real.pi / 2,
        Real.cos (2 * (n : ℝ) * x) := by
    by_cases hn0 : n = 0
    · subst n
      simpa using integral_sinc_sq_eq_pi_div_two
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      rw [integral_sinc_sq_mul_cos_two_nat n hn,
          intervalIntegral_cos_two_nat n hn]

  -- We will interchange the finite sum and the improper integral.
  -- For this, every weighted cosine mode must be integrable.
  have hmode_integrable (n : ℕ) :
      IntegrableOn
        (fun x : ℝ =>
          (Real.sinc x) ^ 2 *
            Real.cos (2 * (n : ℝ) * x))
        (Set.Ioi 0) := by
    apply integrableOn_sinc_sq_mul
    · fun_prop
    · refine ⟨1, zero_le_one, ?_⟩
      intro x
      exact abs_cos_le_one _
  unfold cosinePolynomial
  -- Distribute the factor `sinc²(x)` over the finite sum.
  simp_rw [Finset.mul_sum]
  -- Interchange the finite sum with the improper integral on `(0, ∞)`.
  rw [MeasureTheory.integral_finset_sum]

  -- Interchange the same finite sum with the interval integral.
  · rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro n hn_mem
      calc
        (∫ x in Set.Ioi 0,
            (Real.sinc x) ^ 2 *
              (a n * Real.cos (2 * (n : ℝ) * x)))
            =
          a n *
            (∫ x in Set.Ioi 0,
              (Real.sinc x) ^ 2 *
                Real.cos (2 * (n : ℝ) * x)) := by
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards with x
              ring
        _ =
          a n *
            (∫ x in (0 : ℝ)..Real.pi / 2,
              Real.cos (2 * (n : ℝ) * x)) := by
              rw [hmode n]
        _ =
          ∫ x in (0 : ℝ)..Real.pi / 2,
            a n * Real.cos (2 * (n : ℝ) * x) := by
              rw [intervalIntegral.integral_const_mul]

    -- Each summand on `[0, π/2]` is interval integrable
    · intro n hn_mem
      exact(by
          fun_prop :
          Continuous
            (fun x : ℝ =>
              a n * Real.cos (2 * (n : ℝ) * x))
        ).intervalIntegrable _ _

   -- Each summand in the improper integral is integrable.
  ·intro n hn_mem
   have h := (hmode_integrable n).const_mul (a n)
   simpa [mul_assoc, mul_left_comm, mul_comm] using h

lemma even_of_periodic_of_reflection
    {f : ℝ → ℝ}
    (hf_periodic : Function.Periodic f Real.pi)
    (hf_reflection : ∀ x : ℝ, f (Real.pi - x) = f x) :
    ∀ x : ℝ, f (-x) = f x := by
  intro x
  calc
    f (-x) = f (Real.pi - (Real.pi + x)) := by
      congr 1
      ring
    _ = f (Real.pi + x) := by
      rw [hf_reflection]
    _ = f (x+Real.pi) := by
      congr 1
      ring
    _ = f x :=  hf_periodic x

/-!
## From periodic functions on `ℝ` to functions on a circle

`AddCircle T` is the real line in which two numbers are identified when
their difference is an integer multiple of `T`. In mathematical notation,

`AddCircle T = ℝ / (Tℤ)`.

Thus, in `AddCircle π`, the real numbers `x`, `x + π`, `x - π`,
and more generally `x + nπ`, represent the same point.
-/

private lemma fourier_pi_apply
    (k : ℤ) (x : ℝ) :
    (fourier (T := Real.pi) k)
        (x : AddCircle Real.pi) =
      Complex.exp
        (((2 * (k : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
  -- Mathlib first expresses the Fourier character with the general
  -- phase `2πkx / T`. Here the circumference is `T = π`.
  rw [fourier_coe_apply]
  -- it is enough to prove that their complex exponents are equal.
  apply congrArg Complex.exp
  apply Complex.ext
  -- The real parts of the two exponents agree.
  · push_cast
    field_simp [Real.pi_ne_zero]
  -- Their imaginary parts agree as well.
  · push_cast
    field_simp [Real.pi_ne_zero]


/--
Consider one Fourier term with coefficient `z`.

We take its real part at `x` and at `-x`, then average the two values.
The sine terms cancel, leaving only

`z.re * cos (2 * k * x)`.
-/
private lemma fourier_pi_symmetrized_term
    (k : ℤ) (z : ℂ) (x : ℝ) :
    (((z • fourier (T := Real.pi) k)
          (x : AddCircle Real.pi)).re +
      ((z • fourier (T := Real.pi) k)
          (-x : AddCircle Real.pi)).re) / 2
      =
    z.re * Real.cos (2 * (k : ℝ) * x) := by
  simp only [ContinuousMap.smul_apply]
  simp only [smul_eq_mul]

   -- Replace the abstract Fourier character at `x` by `exp(2ikx)`.
  rw [fourier_pi_apply k x]

  -- Perform the same replacement at the opposite point `-x`.
  have hfourier_neg :
    (fourier (T := Real.pi) k) (-(x : AddCircle Real.pi))
    = Complex.exp (((2 * (k : ℝ) * (-x) : ℝ) : ℂ) * Complex.I) := by
    simpa using fourier_pi_apply k (-x)
  rw [hfourier_neg]

  -- Expand the real part of the complex products and use
  -- `exp(iθ) = cos θ + i sin θ`.
  simp only [
    Complex.mul_re,
    Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im
  ]

  rw [show 2 * (k : ℝ) * (-x) =
      -(2 * (k : ℝ) * x) by ring]
  rw [Real.cos_neg, Real.sin_neg]
  ring

/--
Replacing an integer frequency `k` by its natural absolute value
does not change the corresponding cosine mode.
-/
private lemma cosine_natAbs
    (k : ℤ) (x : ℝ) :
    Real.cos (2 * (k.natAbs : ℝ) * x) =
      Real.cos (2 * (k : ℝ) * x) := by
  cases k with
  | ofNat n =>
      simp
  | negSucc n =>
      rw [show
        2 * ((Int.negSucc n : ℤ) : ℝ) * x =
          -(2 * ((n + 1 : ℕ) : ℝ) * x) by
            push_cast
            ring]
      simp [Real.cos_neg]

  -- Construct the cosine coefficients from the Fourier coefficients.
  -- The Fourier polynomial encoded by `d` is
  --   Q(x) = ∑ k : ℤ, dₖ * exp (2 * k * x * i).
  -- We want to describe its even real part:

  --   (Re(Q(x)) + Re(Q(-x))) / 2 = ∑ k : ℤ, Re(dₖ) * cos (2 * k * x).
  --   cₙ = ∑ k : ℤ, k.natAbs = n, Re(dₖ).
  --
  -- Equivalently,
  --
  --   c₀ = Re(d₀),
  --   cₙ = Re(dₙ) + Re(d₋ₙ)    for n > 0.
lemma finsupp_fourier_symmetrization
    (d : ℤ →₀ ℂ) :
    ∃ c : ℕ →₀ ℝ,
      ∀ x : ℝ,
        c.sum
            (fun n b =>
              b * Real.cos (2 * (n : ℝ) * x))
          =
        (((d.sum
              (fun k z =>
                z • fourier (T := Real.pi) k))
              (x : AddCircle Real.pi)).re +
         ((d.sum
              (fun k z =>
                z • fourier (T := Real.pi) k))
              (-x : AddCircle Real.pi)).re) / 2 := by
  classical

  let c : ℕ →₀ ℝ :=
    d.sum
      (fun k z =>
        Finsupp.single k.natAbs z.re)

  refine ⟨c, ?_⟩
  intro x

  dsimp only [c]

  -- Prove the identity by linear induction on the finitely supported
  -- Fourier coefficient family.
  induction d using Finsupp.induction_linear with

  -- The zero coefficient family represents the zero function on both
  -- sides.
  | zero =>
      simp

  -- In the addition case, prove that the coefficient construction,
  -- the cosine evaluation, and the Fourier evaluation are all additive.
  | add d₁ d₂ hd₁ hd₂ =>
      have h_coeff :(d₁ + d₂).sum
                (fun k z => Finsupp.single k.natAbs z.re)
                = d₁.sum (fun k z => Finsupp.single k.natAbs z.re)
                +d₂.sum (fun k z => Finsupp.single k.natAbs z.re)
                := by
        exact Finsupp.sum_add_index'
           (f := d₁) (g := d₂) (h := fun k z =>Finsupp.single k.natAbs z.re)
          (by
            intro k
            simp)
          (by
            intro k z₁ z₂
            simp [Complex.add_re])

      -- Evaluating the resulting cosine coefficient family is also
      -- additive.
      have h_sum : (((d₁ + d₂).sum
                  (fun k z => Finsupp.single k.natAbs z.re)).sum
                  (fun n b => b * Real.cos (2 * (n : ℝ) * x)))
                  =(d₁.sum (fun k z => Finsupp.single k.natAbs z.re)).sum
                  (fun n b => b * Real.cos (2 * (n : ℝ) * x))
                  +(d₂.sum (fun k z => Finsupp.single k.natAbs z.re)).sum
                  (fun n b => b * Real.cos (2 * (n : ℝ) * x)) := by
        rw [h_coeff]
        exact Finsupp.sum_add_index'
          (f := d₁.sum (fun k z => Finsupp.single k.natAbs z.re))
          (g := d₂.sum (fun k z => Finsupp.single k.natAbs z.re))
          (h := fun n b => b * Real.cos (2 * (n : ℝ) * x))
          (by
            intro n
            simp)
          (by
            intro n b₁ b₂
            ring)

      have h_fourier : (d₁ + d₂).sum
              (fun k z => z • fourier (T := Real.pi) k)
              = d₁.sum (fun k z => z • fourier (T := Real.pi) k)
              + d₂.sum (fun k z => z • fourier (T := Real.pi) k) := by
        apply Finsupp.sum_add_index'
        · intro k
          simp
        · intro k z₁ z₂
          change
            (z₁ + z₂) • fourier (T := Real.pi) k =
              z₁ • fourier (T := Real.pi) k +
              z₂ • fourier (T := Real.pi) k
          exact add_smul z₁ z₂ (fourier (T := Real.pi) k)

      rw [h_sum, hd₁, hd₂, h_fourier]
      simp only [
        ContinuousMap.add_apply,
        Complex.add_re
      ]
      ring

  -- It remains to prove the identity for one Fourier coefficient.
  | single k z =>
      -- Both finitely supported sums reduce to their unique nonzero
      -- term.
      simp only [
        Finsupp.sum_single_index,
        Complex.zero_re,
        Finsupp.single_zero,
        zero_mul,
        zero_smul,
        ContinuousMap.smul_apply
      ]

      -- Replace the natural frequency `|k|` by the integer frequency
      -- `k`, then apply the one-frequency symmetrization identity.
      rw [cosine_natAbs k x]
      exact
        (fourier_pi_symmetrized_term k z x).symm

lemma exists_finsupp_cosine_uniform_approx
    {f : ℝ → ℝ}
    (hf_cont : Continuous f)
    (hf_periodic : Function.Periodic f Real.pi)
    (hf_even : Function.Even f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ →₀ ℝ, ∀ x : ℝ,
      |f x -
      c.sum (fun n b => b * Real.cos (2 * (n : ℝ) * x))|
       < ε := by
  classical
  -- The Fourier theory of `AddCircle T` requires the period `T` to be
  -- positive.
  letI : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

  -- The two endpoints of the fundamental interval represent the same point
  have hendpoint : f 0 = f Real.pi := by
    simpa using (hf_periodic 0).symm

   /-
  The continuous function induced by `f` on `AddCircle π`.
  -/

  -- A `π`-periodic function on `ℝ` can be regarded as a function on the
  -- quotient circle `AddCircle π`.
  --
  -- `liftIco` chooses the representative in `[0, π)`. The endpoint
  -- equality proved above ensures continuity where `0` and `π` are
  -- identified. We use complex values because Mathlib's Fourier density
  -- theorem is formulated over `ℂ`.
  let F : C(AddCircle Real.pi, ℂ) :=
    {
      toFun :=
        fun z =>
         ((AddCircle.liftIco Real.pi 0 f z : ℝ) : ℂ)
      continuous_toFun :=
        Complex.continuous_ofReal.comp
          (AddCircle.liftIco_zero_continuous
            hendpoint
            hf_cont.continuousOn)
    }
  /-
  The lift agrees with `f` on every real representative.
  -/
  have hF_apply (x : ℝ) :
      F (x : AddCircle Real.pi) = (f x : ℂ) := by

    -- Choose the representative `y` of `x` in the fundamental interval
    -- `[0, π)`.
    obtain ⟨n, hn⟩ := exists_mod_pi_mem_Ico x
    let y : ℝ := x - (n : ℝ) * Real.pi
    have hy : y ∈ Set.Ico (0 : ℝ) Real.pi := by
      exact hn

    -- The real numbers `x` and `y = x - nπ` represent the same point of the quotient circle
    have hcoe : (y : AddCircle Real.pi) =
                (x : AddCircle Real.pi) := by
      dsimp [y]
      rw [← zsmul_eq_mul Real.pi n]
      rw [AddCircle.coe_zsmul Real.pi]
      rw [AddCircle.coe_period Real.pi]
      simp

    -- Periodicity also guarantees that `f y = f x`.
    have hperiodic : f y = f x := by
      symm
      convert
        periodic_int_mul_pi
          hf_periodic n y
        using 1
      · dsimp [y]
        ring

    -- Evaluate the lifted function using the representative `y`, then
    -- return to the original value at `x`.
    calc
      F (x : AddCircle Real.pi)
          = F (y : AddCircle Real.pi) := by
              rw [hcoe]
      _ = (f y : ℂ) := by
            simp [
              F,
              AddCircle.liftIco_zero_coe_apply hy
            ]
      _ = (f x : ℂ) := by rw [hperiodic]

   /-
  The finite Fourier span is dense in
  `C(AddCircle π, ℂ)`.
  -/

  -- Let `S` be the space of all finite complex linear combinations of
  -- Fourier characters. Its elements are complex trigonometric
  -- polynomials on the circle.
  let S : Submodule ℂ C(AddCircle Real.pi, ℂ) :=
    Submodule.span ℂ
      (Set.range
        (fourier :
          ℤ → C(AddCircle Real.pi, ℂ)))

  -- The Fourier density theorem says that every continuous function on
  -- the circle is a uniform limit of elements of `S`.
  have hS_dense : Dense (S : Set C(AddCircle Real.pi, ℂ)) := by
    apply
      (Submodule.dense_iff_topologicalClosure_eq_top).2
    simpa [S] using
      (span_fourier_closure_eq_top
        (T := Real.pi))

  -- Choose a Fourier polynomial `P` whose uniform distance from `F` is
  -- less than `ε`.
  obtain ⟨P, hPmem, hFP⟩ := hS_dense.exists_dist_lt F hε

  -- Since `P` belongs to the algebraic Fourier span, it is represented
  -- by a finitely supported family of coefficients `d : ℤ →₀ ℂ`
  obtain ⟨d, hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hPmem
  -- Write the corresponding Fourier polynomial explicitly.
  let Q : C(AddCircle Real.pi, ℂ) :=
    d.sum (fun k z => z • fourier (T := Real.pi) k)

  -- The explicit polynomial `Q` is the element `P` chosen by density,
  -- and hence is uniformly close to `F`.
  have hFQ : dist F Q < ε := by
    have hQP : Q = P := by
      exact hd
    rw [hQP]
    exact hFP
  have hnorm : ‖F - Q‖ < ε := by
    simpa [dist_eq_norm] using hFQ
  have hpointwise
      (z : AddCircle Real.pi) :
      ‖F z - Q z‖ < ε := by
    calc
      ‖F z - Q z‖
          = ‖(F - Q) z‖ := by rfl
      _ ≤ ‖F - Q‖ :=
        ContinuousMap.norm_coe_le_norm
          (F - Q) z
      _ < ε := hnorm

  -- Symmetrize the real part of `Q` and rewrite it as a finitely
  -- supported cosine sum.
  obtain ⟨c, hc⟩ := finsupp_fourier_symmetrization d
  refine ⟨c, ?_⟩
  intro x

  -- The real part of `Q(x)` approximates the real value `f(x)`.
  -- This follows from `|Re z| ≤ ‖z‖`.
  have hxerr :
      |f x -
        (Q (x : AddCircle Real.pi)).re| < ε := by
    have hre :=
      Complex.abs_re_le_norm
        (F (x : AddCircle Real.pi) -
        Q (x : AddCircle Real.pi))
    have hre' :
      |f x - (Q (x : AddCircle Real.pi)).re|
        ≤
      ‖F (x : AddCircle Real.pi) - Q (x : AddCircle Real.pi)‖ := by
      simpa [hF_apply] using hre
    have hp := hpointwise (x : AddCircle Real.pi)
    exact lt_of_le_of_lt hre' hp

  -- Apply the same pointwise estimate at `-x`. Since `f` is even,
  -- `f(-x)` is again equal to the target value `f(x)`.
  have hnegerr :
      |f x -(Q (-x : AddCircle Real.pi)).re| < ε := by
    have hre := Complex.abs_re_le_norm
        (F (-x : AddCircle Real.pi) -
          Q (-x : AddCircle Real.pi))
    have hp := hpointwise (-x : AddCircle Real.pi)
    have hF_neg :
        F (-(x : AddCircle Real.pi)) = (f (-x) : ℂ) := by
      rw [← AddCircle.coe_neg]
      exact hF_apply (-x)
    have hre' : |f (-x) - (Q (-x : AddCircle Real.pi)).re|
      ≤ ‖F (-x : AddCircle Real.pi) -
      Q (-x : AddCircle Real.pi)‖ := by
      simpa only [
        Complex.sub_re,
        hF_neg,
        Complex.ofReal_re
      ] using hre
    have hraw :
    |f (-x) - (Q (-x : AddCircle Real.pi)).re| < ε :=
    lt_of_le_of_lt hre' hp
    simpa [hf_even x] using hraw

  rw [hc x]

  -- The cosine polynomial constructed by `hc` is the average of
  -- `Re Q(x)` and `Re Q(-x)
  let A : ℝ := (Q (x : AddCircle Real.pi)).re
  let B : ℝ := (Q (-x : AddCircle Real.pi)).re
  change |f x - (A + B) / 2| < ε

  calc |f x - (A + B) / 2| =
  |((f x - A) + (f x - B)) / 2| := by
        congr 1
        ring
  _ =|(f x - A) + (f x - B)| / 2 := by
        rw [abs_div]
        norm_num
  _ ≤ (|f x - A| + |f x - B|) / 2 := by
        apply (div_le_div_iff_of_pos_right
          (by norm_num : (0 : ℝ) < 2)).2
        exact abs_add_le (f x - A) (f x - B)
  _ < (ε + ε) / 2 := by
        apply (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
        exact add_lt_add hxerr hnegerr
  _ =ε := by simp

/--
Uniformly approximates a continuous, `π`-periodic function satisfying
the reflection symmetry `f (π - x) = f x` by cosine polynomials.

Periodicity and reflection symmetry first imply that `f` is even.
The general cosine approximation theorem can then be applied.
-/
lemma exists_cosinePolynomial_uniform_approx
    {f : ℝ → ℝ}
    (hf_cont : Continuous f)
    (hf_periodic : Function.Periodic f Real.pi)
    (hf_even : Function.Even f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ a : ℕ → ℝ, ∀ x : ℝ,
      |f x - cosinePolynomial N a x| < ε := by
  classical
  obtain ⟨c, hc⟩ :=
  exists_finsupp_cosine_uniform_approx hf_cont hf_periodic hf_even hε
  let N : ℕ := c.support.sup id
  let a : ℕ → ℝ := fun n => c n

  refine ⟨N, a, ?_⟩
  intro x

  have hsupp :
      c.support ⊆ Finset.range (N + 1) := by
    intro n hn
    rw [Finset.mem_range]
    have hnN : n ≤ N := by
      dsimp [N]
      exact Finset.le_sup (f := id) hn
    omega

  have hsum :
    c.sum (fun n b => b * Real.cos (2 * (n : ℝ) * x))
        = cosinePolynomial N a x := by
    unfold cosinePolynomial
    change ( ∑ n ∈ c.support, c n * Real.cos (2 * (n : ℝ) * x)
    =∑ n ∈ Finset.range (N + 1), a n * Real.cos (2 * (n : ℝ) * x))
    apply Finset.sum_subset hsupp
    intro n hn_range hn_support
    have hcn : c n = 0 :=
      Finsupp.notMem_support_iff.mp hn_support
    simp [a, hcn]

  rw [← hsum]
  exact hc x

lemma exists_cosinePolynomial_uniform_approx_of_reflection
    {f : ℝ → ℝ}
    (hf_cont : Continuous f)
    (hf_periodic : Function.Periodic f Real.pi)
    (hf_reflection : ∀ x : ℝ, f (Real.pi - x) = f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ a : ℕ → ℝ,
      ∀ x : ℝ,
        |f x - cosinePolynomial N a x| < ε := by

  -- Start with the finitely supported cosine approximation constructed
  -- from Fourier density.
  apply exists_cosinePolynomial_uniform_approx
      hf_cont hf_periodic
  · intro x
    calc
      f (-x) = f (-x + Real.pi) := (hf_periodic (-x)).symm
      _ = f (Real.pi - x) := by
        congr 1
        ring
      _ = f x := hf_reflection x
  · exact hε

 -- A continuous periodic function is bounded, so multiplication by it
  -- preserves the integrability of `sinc²`.
lemma integrableOn_sinc_sq_mul_of_periodic
    {f : ℝ → ℝ}
    (hf_cont : Continuous f)
    (hf_periodic : Function.Periodic f Real.pi) :
    IntegrableOn
      (fun x : ℝ => (Real.sinc x) ^ 2 * f x)
      (Set.Ioi 0) := by
  apply integrableOn_sinc_sq_mul hf_cont (bounded_of_continuous_periodic_pi hf_cont hf_periodic)

lemma abs_integral_sinc_sq_mul_sub_le
    {f g : ℝ → ℝ}
    (hf_int :
      IntegrableOn
        (fun x : ℝ => (Real.sinc x) ^ 2 * f x)
        (Set.Ioi 0))
    (hg_int :
      IntegrableOn
        (fun x : ℝ => (Real.sinc x) ^ 2 * g x)
        (Set.Ioi 0))
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hfg : ∀ x : ℝ, |f x - g x| ≤ ε) :
    |(∫ x in Set.Ioi 0,
        (Real.sinc x) ^ 2 * f x) -
      (∫ x in Set.Ioi 0,
        (Real.sinc x) ^ 2 * g x)|
      ≤ (Real.pi / 2) * ε := by
  have hsub_int :
    IntegrableOn (fun x : ℝ =>
    (Real.sinc x) ^ 2 * f x - (Real.sinc x) ^ 2 * g x)
    (Set.Ioi 0) := hf_int.sub hg_int
  have hmajor_int :
    IntegrableOn (fun x : ℝ => (Real.sinc x) ^ 2 * ε)
    (Set.Ioi 0) :=integrable_sinc_sq.mul_const ε
  rw [← integral_sub hf_int hg_int]
  calc |∫ x in Set.Ioi 0,
        ((Real.sinc x) ^ 2 * f x -
         (Real.sinc x) ^ 2 * g x)|
    ≤ ∫ x in Set.Ioi 0,
        |(Real.sinc x) ^ 2 * f x -
         (Real.sinc x) ^ 2 * g x| := by
        exact abs_integral_le_integral_abs
  _ ≤ ∫ x in Set.Ioi 0,(Real.sinc x) ^ 2 * ε := by
        apply integral_mono_ae hsub_int.abs hmajor_int
        filter_upwards with x
        rw [← mul_sub, abs_mul, abs_sq ]
        gcongr
        exact hfg x
  _ = (Real.pi / 2) * ε := by
        rw [integral_mul_const]
        rw [integral_sinc_sq_eq_pi_div_two]

lemma abs_intervalIntegral_sub_le
    {f g : ℝ → ℝ}
    (hf_cont : Continuous f)
    (hg_cont : Continuous g)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hfg : ∀ x : ℝ, |f x - g x| ≤ ε) :
    |(∫ x in (0 : ℝ)..Real.pi / 2, f x) -
      (∫ x in (0 : ℝ)..Real.pi / 2, g x)|
      ≤ (Real.pi / 2) * ε := by
  have hπ : (0 : ℝ) ≤ Real.pi / 2 := by
    positivity

  have hf_int :
      IntervalIntegrable f volume 0 (Real.pi / 2) :=
    hf_cont.intervalIntegrable 0 (Real.pi / 2)

  have hg_int :
      IntervalIntegrable g volume 0 (Real.pi / 2) :=
    hg_cont.intervalIntegrable 0 (Real.pi / 2)

  have hsub_int :
      IntervalIntegrable
        (fun x : ℝ => f x - g x)
        volume 0 (Real.pi / 2) :=
    hf_int.sub hg_int

  rw [← intervalIntegral.integral_sub hf_int hg_int]

  calc
    |∫ x in (0 : ℝ)..Real.pi / 2, f x - g x|
        ≤ ∫ x in (0 : ℝ)..Real.pi / 2,
            |f x - g x| := by
          exact
            intervalIntegral.abs_integral_le_integral_abs hπ

    _ ≤ ∫ _x in (0 : ℝ)..Real.pi / 2, ε := by
          apply intervalIntegral.integral_mono_on
            hπ
            hsub_int.abs
            intervalIntegrable_const
          intro x hx
          exact hfg x

    _ = (Real.pi / 2) * ε := by
          simp [smul_eq_mul]


/--
Extends Lobachevsky's identity from cosine polynomials to any continuous
function that can be uniformly approximated by cosine polynomials.
-/
lemma lobachevsky_of_uniform_cosine_approx
    {f : ℝ → ℝ}
    (hf_cont : Continuous f)
    (hf_int :
      IntegrableOn
        (fun x : ℝ => (Real.sinc x) ^ 2 * f x)
        (Set.Ioi 0))
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ a : ℕ → ℝ,
          ∀ x : ℝ,
            |f x - cosinePolynomial N a x| < ε) :
    (∫ x in Set.Ioi 0,
      (Real.sinc x) ^ 2 * f x)
      =
    ∫ x in (0 : ℝ)..Real.pi / 2, f x := by
  let Lf : ℝ :=
    ∫ x in Set.Ioi 0, (Real.sinc x) ^ 2 * f x
  let Rf : ℝ :=
    ∫ x in (0 : ℝ)..Real.pi / 2, f x
  change Lf = Rf

   -- Assume that the two integrals are different and derive a
  -- contradiction from uniform approximation.
  by_contra hne


  have hd_pos : 0 < |Lf - Rf| := by
    exact abs_pos.mpr (sub_ne_zero.mpr hne)

  -- Choose the approximation error so that `π η` is exactly half of
  -- the alleged positive difference.
  let η : ℝ :=
    |Lf - Rf| / (2 * Real.pi)
  have hη : 0 < η := by
    dsimp [η]
    positivity

  -- Choose a cosine polynomial approximating `f` uniformly within `η`.
  obtain ⟨N, a, ha⟩ := happrox η hη

  let p : ℝ → ℝ := cosinePolynomial N a
  have hp_cont : Continuous p := by
    dsimp [p]
    exact continuous_cosinePolynomial N a
  have hp_int :IntegrableOn (fun x : ℝ => (Real.sinc x) ^ 2 * p x)
        (Set.Ioi 0) := by
    simpa [p] using
    integrableOn_sinc_sq_mul_cosinePolynomial N a
  have hfp : ∀ x : ℝ, |f x - p x| ≤ η := by
    intro x
    exact (by simpa [p] using (ha x).le)
  have hpf : ∀ x : ℝ, |p x - f x| ≤ η := by
    intro x
    rw [abs_sub_comm]
    exact hfp x

  -- Define the two integrals evaluated at the approximating polynomial.
  let Lp : ℝ :=
    ∫ x in Set.Ioi 0, (Real.sinc x) ^ 2 * p x
  let Rp : ℝ :=
    ∫ x in (0 : ℝ)..Real.pi / 2, p x

  -- Lobachevsky's identity has already been proved for every cosine
  -- polynomial.
  have hp_eq : Lp = Rp := by
    dsimp [Lp, Rp, p]
    exact lobachevsky_cosinePolynomial N a
  have hL : |Lf - Lp| ≤ (Real.pi / 2) * η := by
    dsimp [Lf, Lp]
    exact abs_integral_sinc_sq_mul_sub_le hf_int hp_int hη.le hfp
  have hR : |Rp - Rf| ≤ (Real.pi / 2) * η := by
    dsimp [Rp, Rf]
    exact abs_intervalIntegral_sub_le hp_cont hf_cont hη.le hpf

  have hbound :
      |Lf - Rf| ≤ Real.pi * η := by
    calc
    |Lf - Rf| = |(Lf - Lp) + (Rp - Rf)| := by
      congr 1
      rw [hp_eq]
      ring
    _ ≤  |(Lf - Lp)| + |(Rp - Rf)| := by
      exact abs_add_le _ _
    _ ≤  (Real.pi / 2) * η + (Real.pi / 2) * η := by
      exact add_le_add hL hR
    _ =  Real.pi  * η := by
      ring

  have hη_value : Real.pi * η = |Lf - Rf| / 2 := by
    dsimp [η]
    field_simp

  linarith

/--
Lobachevsky's integral formula for the square of `sinc`.

If `f` is continuous, `π`-periodic, and symmetric under
`x ↦ π - x`, then

`∫₀^∞ sinc²(x) f(x) dx = ∫₀^{π/2} f(x) dx`.

The proof has three main ingredients:

1. periodicity and reflection symmetry imply that `f` is even;
2. such a function can be uniformly approximated by finite cosine
   polynomials using Fourier approximation on `AddCircle π`;
3. Lobachevsky's identity is known for cosine polynomials and passes
   to the uniform limit through the two integral estimates.
-/
theorem lobachevsky_integral_formula
    {f : ℝ → ℝ}
    (hf_cont : Continuous f)
    (hf_periodic : Function.Periodic f Real.pi)
    (hf_reflection : ∀ x : ℝ, f (Real.pi - x) = f x) :
    (∫ x in Set.Ioi 0,
      (Real.sinc x) ^ 2 * f x)
      =
    ∫ x in (0 : ℝ)..Real.pi / 2, f x := by
  have hf_bounded :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |f x| ≤ C :=
    bounded_of_continuous_periodic_pi
      hf_cont hf_periodic
  have hf_int : IntegrableOn
        (fun x : ℝ => (Real.sinc x) ^ 2 * f x)
        (Set.Ioi 0) :=
      integrableOn_sinc_sq_mul hf_cont hf_bounded
  apply lobachevsky_of_uniform_cosine_approx hf_cont hf_int

  intro ε hε
  exact exists_cosinePolynomial_uniform_approx_of_reflection
    hf_cont
    hf_periodic
    hf_reflection
    hε

end Lobachevsky
