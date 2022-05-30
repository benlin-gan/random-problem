import data.real.basic
import tactic

open_locale classical
open set
open function
@[simp] def positive_reals := {x : ℝ | x > 0}
@[simp] def continuous (f : ℝ → ℝ): Prop := 
  ∀(ε ∈ positive_reals), ∀(c: ℝ), ∃(δ ∈ positive_reals), ∀(x y : ℝ), 
  (abs (x - c) ≤ δ) → (abs (y -c) ≤ δ ) → (abs (f x - f y) < ε) 
@[simp] def sublinear (f : ℝ → ℝ) : Prop := 
  ∀ (x: ℝ), ∃{c d : ℝ}, abs (f x) < c + d * abs x 
@[simp] def get_real  : ℕ → ℝ 
| 0       := (0: ℝ)
| (n + 1) := get_real n + (1 : ℝ) 
lemma zongshu {f: ℝ → ℝ} (k: ℕ): 
  (continuous f) → ∃(δ ∈ positive_reals),
    ∀x, (abs x ≤ (get_real k * δ)) → (abs (f x - f 0) ≤ get_real k):=
begin 
  intro cf,
  have og : (1 : ℝ) > 0 := by norm_num, --one is greater than zero
  have εeq1 := cf 1 og, --definition of continuity with 1 plugged in for epsilon
  induction k with k ind, --induction on k,
  {
    --base case is basically just expand the hypotheses
    --and the zeros cancel everything out so it's trivial
    rcases εeq1 0 with ⟨δ, ⟨δpos, q⟩⟩, 
    use [δ, δpos], 
    simp only [get_real], --replace (0 : ℕ) with (0 : ℝ)
    rw zero_mul,
    intros x h,
    --abs x ≤ 0 implies x = 0 
    have h' := abs_eq_zero.mp (le_antisymm h (abs_nonneg x)), 
    rw h',
    rw sub_self (f 0),
    convert (le_refl (0 : ℝ)),
    rw abs_eq_zero,
  },
  {
    rcases ind with ⟨δ, ⟨δpos, ind⟩⟩,
    use [δ, δpos],
    intros x h,
    simp at h,
    rw add_mul at h,
    rw one_mul at h,
    simp,
    rcases εeq1 (x) with ⟨δ₂, ⟨δ₂pos, r⟩⟩,
    have bruh : abs δ ≤ δ₂, {sorry}, 
    --a step I skipped
    --δ comes from the inductive hypothesis 
    --δ₂ 

    --h' comes from subtracting δ from both sides of h
    have h' : abs (x) - δ ≤ get_real k * δ := by linarith,
    cases lt_or_ge δ x with xbig δbig,
    {
      --if x > δ: x - δ was the center of the previous case
      have prev := ind (x - δ),
      have next := r (x) (x - δ),

      --do some cancelations
      rw sub_self at next,
      rw abs_zero at next,
      have next' := next (le_of_lt δ₂pos),

      --do more cancellations
      rw sub_sub_cancel_left at next',
      rw abs_neg at next',
      have next'' := le_of_lt (next' bruh),


      dsimp at δpos,
      --x is positive because it's bigger than δ which is positive
      have xpos := lt_trans δpos xbig,
      rw abs_of_pos xpos at h', --so we eliminate the absolute value here
      have cool : x - δ > 0 := by linarith, -- subtract δpos from xpos
      rw ← abs_of_pos cool at h', --put absolute value around x - δ
      have prev' := prev h', --to satisfy the conditions of prev


      have final := add_le_add prev' next'',
      have := abs_sub_le (f x) (f (x- δ)) (f 0), --triangle inequality
      rw add_comm at this,
      exact le_trans this final,
    },
    {
      cases le_or_gt (-x) δ with negxsmall negxbig,
      {
        have constraints := abs_le'.mpr ⟨δbig, negxsmall⟩,
        --another step I skipped
        --happens when |x| < δ 
        --shouldn't really happen, because δ can get arbitrarily small???
        sorry,
      },

      --this case is where x is negative
      --and it's absolute value is larger than δ 

      --in this case, x + δ is the center of the previous case
      have prev := ind (x + δ),
      have next := r x (x + δ),

      --do cancellations
      rw sub_self at next,
      rw abs_zero at next,
      have next' := next (le_of_lt δ₂pos),

      --and more cancellation
      rw add_sub_cancel' at next',
      have next'' := le_of_lt (next' bruh),

      have c : abs (x + δ) = abs x - δ,
      {
        have d : (x + δ) < 0 := by linarith, --add x to both sides of nexbig
        rw abs_of_neg d, --replace absolute value with negative
        have xneg : x < 0 := by linarith, 
        rw abs_of_neg xneg, --replace absolute value with negative
        ring,
      },
      rw ← c at h', --all that to get h' in the right form
      have prev' := prev h', --to extract another inequality

      have final := add_le_add prev' next'',
      have := abs_sub_le (f x) (f (x + δ)) (f 0), --trinagle inequality again
      rw add_comm at this,
      exact le_trans this final,
    },
  },
end
example {f: ℝ → ℝ}: (continuous f) → (sublinear f) := 
begin 
  sorry
  --and we still have to prove this too :C
end 