import LaplaceTransform.DirichletIntegral



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
