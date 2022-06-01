import data.real.basic
import data.real.nnreal
import tactic

open_locale classical
@[simp] def pos_real := {x : ℝ | 0 < x},
def uni_cont (f : ℝ → ℝ) : Prop :=
  ∀ε ∈ pos_real, ∃δ ∈ pos_real, ∀(x y: ℝ),
  abs(x - y) ≤ δ → abs(f x - f y) ≤ ε
def sublinear (f : ℝ → ℝ) : Prop := 
  ∀ (x: ℝ), ∃{c d : ℝ}, abs (f x) < c + d * abs x 
example {f : ℝ → ℝ} : (uni_cont f) → (sublinear f) :=
begin
  intro ucf,
  have og : 0 < (1 : ℝ) := by linarith,
  have ε1 := ucf 1 og,
  rcases ε1 with ⟨δ, ⟨δpos, bound⟩⟩,
  dsimp at δpos,
  have nbound : ∀(k : ℤ), abs (f (↑k * δ)) ≤ abs(f 0) + abs ↑k,
  {
    intro k,
    induction k with k k, --splits into naturals and neg naturals
    {
      induction k with k ih, --splits into zero and successor of nat
      {
        rw int.of_nat_zero,
        rw int.cast_zero,
        rw zero_mul,
        rw abs_zero,
        rw add_zero,
      },
      {
        have next := bound ((↑k + 1) * δ)(↑k * δ),
        rw add_mul at next,
        rw one_mul at next,
        rw add_sub_cancel' at next,
        rw abs_of_pos δpos at next,
        have next' := next (le_refl δ),
        have triangle := abs_sub_le 0 (f(↑k * δ)) (f ((↑k + 1) * δ)),
          rw zero_sub at triangle,
          rw zero_sub at triangle,
          rw abs_neg at triangle,
          rw abs_neg at triangle,
        have combined := add_le_add ih next',
        apply le_trans triangle,
        rw abs_sub_comm,
        rw add_assoc at combined,
        convert combined,
        rw add_mul,
        rw one_mul,
        simp,
        have q := nnreal.coe_nonneg k, --so much bs
        rw nnreal.coe_nat_cast k at q, --I hate it here
        linarith,
      },
    },
    {
      induction k with k ih, --splits into k = -1 and its negative successors
      {
        simp, --eliminate bs
        have bneg1 := bound (-δ) 0,
        rw sub_zero at bneg1,
        rw abs_neg at bneg1,
        rw abs_of_pos δpos at bneg1,
        have bneg1' := bneg1 (le_refl δ),
        have triangle := abs_sub_le 0 (f 0) (f (-δ)),
          rw zero_sub at triangle,
          rw zero_sub at triangle,
          rw abs_neg at triangle,
          rw abs_neg at triangle,
          rw abs_sub_comm at triangle,
        linarith,
      },
      {
        have next := bound (↑-[1+k.succ]*δ) (↑-[1+k]*δ),
          simp at next,
          rw ← sub_mul at next,
          rw add_sub_cancel at next,
          rw neg_one_mul at next,
          rw abs_neg at next,
          rw abs_of_pos δpos at next,
        have next' := next (le_refl δ),
        have triangle := abs_sub_le 0 (f (↑-[1+k]*δ)) (f (↑-[1+k.succ]*δ)),
        simp at triangle,
        simp,
        apply le_trans triangle,
        have combined := add_le_add ih next',
        simp at combined,
        rw abs_sub_comm at combined,
        rw add_assoc at combined,
        convert combined, --qed, the rest is trivial
        rw ← neg_add,
        rw ← neg_add,
        rw abs_neg,
        rw abs_neg,
        have q := nnreal.coe_nonneg k, --so much bs
        rw nnreal.coe_nat_cast k at q,
        have t: 0 ≤ (1 :ℝ) + ↑k := by linarith,
        have t': 0 ≤ (1 :ℝ) + (1 + ↑k) := by linarith, 
        rw abs_of_nonneg t,
        rw abs_of_nonneg t',
        ring,
      }
    }
  },
  intro x,
  have near_int : ∃(n : ℤ), abs(x - n * δ) ≤ δ ∧ (abs (↑n) * δ) < abs x,
  {
    sorry,
  },
  rcases near_int with ⟨n, ⟨a, int_bound⟩⟩, 
  have q := nbound n,
  have b := bound x (n * δ) a,
  have triangle := abs_sub_le 0 (f (n * δ)) (f x),
  rw zero_sub at triangle,
  rw zero_sub at triangle,
  rw abs_neg at triangle,
  rw abs_neg at triangle,
  rw abs_sub_comm at triangle,
  
  have b' := add_le_add (le_refl (abs(f (n * δ)))) b,
  have triangle' := le_trans triangle b',
  use [abs (f 0) + 1, 1/δ],
  have q' := add_le_add q (le_refl 1),
  have triangle'' := le_trans triangle' q',
  apply lt_of_le_of_lt triangle'',
  have := (lt_div_iff δpos).mpr int_bound,
  rw ←  mul_div_right_comm,
  rw one_mul,
  linarith,
end