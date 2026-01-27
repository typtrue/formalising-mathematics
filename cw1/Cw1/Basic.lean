import Mathlib.Tactic

set_option linter.style.commandStart false

/-
  Definitions
-/

/-- define monotone increasing sequences -/
def is_monotone_increasing (a : ℕ → ℝ) : Prop :=
  ∀ (n m : ℕ), n ≤ m → a n ≤ a m

/-- define an upper bound -/
def is_upper_bound (a : ℕ → ℝ) (K : ℝ) : Prop :=
  ∀ (n : ℕ), K ≥ a n

/-- define what it means for a sequence to be bounded above -/
def is_bounded_above (a : ℕ → ℝ) : Prop :=
  ∃ (K : ℝ), is_upper_bound a K

/-- define monotone decreasing sequences -/
def is_monotone_decreasing (a : ℕ → ℝ) : Prop :=
  ∀ (n m : ℕ), n ≤ m → a m ≤ a n

/-- define a lower bound -/
def is_lower_bound (a : ℕ → ℝ) (K : ℝ) : Prop :=
  ∀ (n : ℕ), a n ≥ K

/-- define what it means for a sequence to be bounded below -/
def is_bounded_below (a : ℕ → ℝ) : Prop :=
  ∃ (K : ℝ), is_lower_bound a K

/--
define bounded monotone sequences
specifically, sequences that are both monotone *increasing* and bounded *above*,
or sequences that are both monotone *decreasing* and bounded *below*
-/
def is_bounded_monotone (a : ℕ → ℝ) : Prop :=
  (is_monotone_increasing a ∧ is_bounded_above a) ∨ (is_monotone_decreasing a ∧ is_bounded_below a)

/-- define whether L is a limit -/
def is_limit (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, |a n - L| < ε

/-- lets us use `rw limit_def` to replace `is_limit a L` with `∀ ε > 0, ∃ (N : ℕ), ...` -/
lemma limit_def (a : ℕ → ℝ) (L : ℝ) :
  is_limit a L ↔ ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, |a n - L| < ε := by rfl

/-- define whether a sequence converges to a limit -/
def is_convergent (a : ℕ → ℝ) : Prop :=
  ∃ (L : ℝ), is_limit a L

/-- lets us use `rw conv_def` to replace `is_convergent a` with `∃ (L : ℝ), is_limit a L` -/
lemma conv_def (a : ℕ → ℝ) :
  is_convergent a ↔ ∃ (L : ℝ), is_limit a L := by rfl

/-- define whether x is a supremum -/
def is_supremum (a : ℕ → ℝ) (x : ℝ) : Prop :=
  is_upper_bound a x ∧
  ∀ (K : ℝ), is_upper_bound a K → x ≤ K

/-- define whether x is an infimum -/
def is_infimum (a : ℕ → ℝ) (x : ℝ) : Prop :=
  is_lower_bound a x ∧
  ∀ (K : ℝ), is_lower_bound a K → K ≤ x

/-
here we assume the completeness of ℝ, which we would otherwise
have to construct using Dedekind cuts
-/

/-- Any sequence in ℝ that is bounded above has a supremum in ℝ.
Taken as an axiom of ℝ due to completeness. -/
axiom bounded_above_has_supremum (a : ℕ → ℝ) :
  is_bounded_above a → ∃ (s : ℝ), is_supremum a s

/-- Any sequence in ℝ that is bounded below has an infimum in ℝ.
Taken as an axiom of ℝ due to completeness. -/
axiom bounded_below_has_infimum (a : ℕ → ℝ):
  is_bounded_below a → ∃ (s : ℝ), is_infimum a s

/-- Any monotone increasing sequence in ℝ with a supremum converges to its supremum. -/
lemma mono_inc_conv_to_sup (a : ℕ → ℝ) (L : ℝ)
    (hMono : is_monotone_increasing a) (hSup : is_supremum a L) :
    is_limit a L := by
{
  -- introduce `ε > 0`
  intro ε hε
  -- break hSup down into its components
  rcases hSup with ⟨hUBound, hLowest⟩
  -- now, we show that `L - ε` cannot be an upper bound of `a`.
  have hLMinusεNotUpper : ¬ is_upper_bound a (L - ε) := by
  {
    intro h
    have hContr := hLowest (L - ε) h
    /-
    we prove this by contradiction: if `L - ε` *is* an upper bound for `a`,
    then `L` cannot be the lowest of such upper bounds (`hLowest`) as
    this implies `L ≤ L - ε` when we have `ε > 0`.
    -/
    linarith
  }
  /-
  we now know that `L - ε` is not an upper bound, so we know that there
  is an `N` such that `a_N ≥ L - ε`.
  -/
  unfold is_upper_bound at hLMinusεNotUpper
  push_neg at hLMinusεNotUpper
  rcases hLMinusεNotUpper with ⟨N, hN⟩
  /-
  we know this `N` works for our definition of convergence, so we
  convert our goal to be to show that it holds for `n > N`.
  -/
  refine ⟨N, ?_⟩
  -- pick `n > N`
  intro n hn
  -- set up bounds `L - ε ≤ a_n ≤ L`
  have hLowerThanL : a n ≤ L := hUBound n
  have hMonoRaw : a N ≤ a n := hMono N n hn
  -- since `a_n - L ≤ 0`, `|a_n - L| = -(a_n - L)`, removing the `|·|`.
  have hAbs : |a n - L| = -(a n - L) := by
  {
    have hAbsZero : a n - L ≤ 0 := by linarith
    exact abs_of_nonpos hAbsZero
  }
  rw [hAbs]
  linarith
}

/-- Any monotone decreasing sequence in ℝ with an infimum converges to its infimum. -/
lemma mono_dec_conv_to_inf (a : ℕ → ℝ) (L : ℝ)
    (hMono : is_monotone_decreasing a) (hSup : is_infimum a L) :
    is_limit a L := by
{
  -- introduce `ε > 0`
  intro ε hε
  -- break hSup down into its components
  rcases hSup with ⟨hLBound, hHighest⟩
  -- now, we show that `L + ε` cannot be an upper bound of `a`.
  have hLPlusεNotLower : ¬ is_lower_bound a (L + ε) := by
  {
    intro h
    have hContr := hHighest (L + ε) h
    /-
    we prove this by contradiction: if `L + ε` *is* a lower bound for `a`,
    then `L` cannot be the highest of such lower bounds (`hHighest`) as
    this implies `L ≥ L + ε` when we have `ε > 0`.
    -/
    linarith
  }
  /-
  we now know that `L + ε` is not a lower bound, so we know that there
  is an `N` such that `a_N ≤ L + ε`.
  -/
  unfold is_lower_bound at hLPlusεNotLower
  push_neg at hLPlusεNotLower
  rcases hLPlusεNotLower with ⟨N, hN⟩
  /-
  we know this `N` works for our definition of convergence, so we
  convert our goal to be to show that it holds for `n > N`.
  -/
  refine ⟨N, ?_⟩
  -- pick `n > N`
  intro n hn
  -- set up bounds `L ≤ a_n ≤ L + ε`
  have hLowerThanL : a n ≥ L := hLBound n
  have hMonoRaw : a n ≤ a N := hMono N n hn
  -- since `a_n - L ≥ 0`, `|a_n - L| = a_n - L`, removing the `|·|`.
  have hAbs : |a n - L| = a n - L := by
  {
    have hAbsZero : a n - L ≥ 0 := by linarith
    exact abs_of_nonneg hAbsZero
  }
  rw [hAbs]
  linarith
}

/-- Any bounded monotone sequence in ℝ converges to a limit in ℝ. -/
theorem monotone_conv (a : ℕ → ℝ) (hBM : is_bounded_monotone a) : is_convergent a := by
{
  -- separate into monotone increasing and decreasing cases
  cases hBM with
  | inl hInc =>
    rcases hInc with ⟨hMono, hBound⟩
    rcases bounded_above_has_supremum a hBound with ⟨L, hL_sup⟩
    exact ⟨L, mono_inc_conv_to_sup a L hMono hL_sup⟩
  | inr hDec =>
    rcases hDec with ⟨hMono, hBound⟩
    rcases bounded_below_has_infimum a hBound with ⟨L, hL_inf⟩
    exact ⟨L, mono_dec_conv_to_inf a L hMono hL_inf⟩
}
