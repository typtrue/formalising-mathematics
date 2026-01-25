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
  ∀ (n : ℕ), K > a n

/-- define what it means for a sequence to be bounded above -/
def is_bounded_above (a : ℕ → ℝ) : Prop :=
  ∃ (K : ℝ), is_upper_bound a K

/-- define monotone decreasing sequences -/
def is_monotone_decreasing (a : ℕ → ℝ) : Prop :=
  ∀ (n m : ℕ), n ≤ m → a m ≤ a n

/-- define a lower bound -/
def is_lower_bound (a : ℕ → ℝ) (K : ℝ) : Prop :=
  ∀ (n : ℕ), a n ≤ K

/-- define what it means for a sequence to be bounded below -/
def is_bounded_below (a : ℕ → ℝ) : Prop :=
  ∃ (K : ℝ), is_lower_bound a K

/--
define bounded monotone sequences
specifically, sequences that are both monotone increasing and bounded above,
or sequences that are both monotone decreasing and bounded below
-/
def is_bounded_monotone (a : ℕ → ℝ) : Prop :=
  (is_monotone_increasing a ∧ is_bounded_above a) ∨ (is_monotone_decreasing a ∧ is_bounded_below a)

/-- define whether L is a limit -/
def is_limit (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ (N : ℕ), ∀ n > N, |a n - L| < ε

/-- define whether a sequence converges to a limit -/
def is_convergent (a : ℕ → ℝ) : Prop :=
  ∃ (L : ℝ), is_limit a L

/-- define whether x is a supremum -/
def is_supremum (a : ℕ → ℝ) (x : ℝ) : Prop :=
  is_upper_bound a x ∧
  ∀ (K : ℝ), is_upper_bound a K → x ≤ K

/-- define whether x is an infimum -/
def is_infimum (a : ℕ → ℝ) (x : ℝ) : Prop :=
  is_lower_bound a x ∧
  ∀ (K : ℝ), is_lower_bound a K → K ≤ x

/-- lets us use `rw limit_def` to replace `is_limit a L` with `∀ ε > 0, ∃ (N : ℕ), ...` -/
lemma limit_def (a : ℕ → ℝ) (L : ℝ) :
  is_limit a L ↔ ∀ ε > 0, ∃ (N : ℕ), ∀ n > N, |a n - L| < ε := by rfl

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
axiom bounded_above_has_infimum (a : ℕ → ℝ):
  is_bounded_below a → ∃ (s : ℝ), is_infimum a s

/-- Any monotone increasing sequence in ℝ with a supremum converges to its supremum. -/
lemma mono_inc_conv_to_sup (a : ℕ → ℝ) (L : ℝ) (hMono : is_monotone_increasing a) (hSup : is_supremum a L) : is_limit a L := by
{
  sorry
}

/-- Any monotone decreasing sequence in ℝ with an infimum converges to its infimum. -/
lemma mono_dec_conv_to_inf (a : ℕ → ℝ) (L : ℝ) (hMono : is_monotone_decreasing a) (hSup : is_infimum a L) : is_limit a L := by
{
  sorry
}

/-- Any bounded monotone sequence in ℝ converges to a limit in ℝ. -/
theorem monotone_conv (a : ℕ → ℝ) (hBM : is_bounded_monotone a) : is_convergent a := by
{
  -- separate into monotone increasing and decreasing cases
  cases hBM with
  | inl hInc =>
    rcases hInc with ⟨hMono, hBound⟩
    sorry
  | inr hDec =>
    rcases hDec with ⟨hMono, hBound⟩
    sorry
}
