import Mathlib.Tactic

-- Bolzano-Weierstrauss for (xₙ) in ℝ

def is_peak (a : ℕ → ℝ) (n : ℕ) :=
  ∀ (m : ℕ) > n, a m ≤ a n

def has_limit () :=
  sorry

-- todo figure out how to make a subsequence + setup sequences
-- properly.
-- maybe ask on edstem / go to office hour if there is one
theorem bolzano_weierstrauss (a : ℕ → ℝ) : ∃ (i : ℕ → ℕ),
    by {
  sorry
}
