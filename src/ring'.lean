import tactic
--proof that the commutativity of addition follows from
--distributivity and commutativity of multiplication
--(plus associativity, inverses, and left and right identities).
class has_group_notation (R : Type) extends has_mul R, has_add R, has_zero R, has_one R, has_neg R
class ring' (R : Type) extends has_group_notation R :=
  (mul_assoc : ∀ (a b c : R), a * b * c = a * (b * c))
  (mul_one : ∀ (a : R), a * 1 = a)
  (mul_comm : ∀(a b : R), a * b = b * a)
  (add_assoc : ∀(a b c : R), a + b + c = a + (b + c))
  (add_zero : ∀(a : R), a + 0 = a)
  (zero_add : ∀(a : R), 0 + a = a)
  (mul_add : ∀(a b c : R), a * (b + c) = a * b + a * c)
  (right_inv : ∀(a : R), a + (-a) = 0)
namespace ring'
variables {R : Type} [ring' R]
lemma right_cancel : ∀{a b c: R}, a + c = b + c → a = b :=
begin
  intros a b c h,
  have start : a + 0 = a,
    exact add_zero a,
  have bruh := right_inv c,
  rw ← bruh at start,
  rw ← add_assoc at start,
  rw h at start,
  rw add_assoc at start,
  rw bruh at start,
  rw add_zero at start,
  symmetry,
  exact start,
end
lemma inv_of_inv : ∀(a : R), -(-a) = a :=
begin 
  intro a,
  have ia := right_inv a,
  have iia := right_inv (-a),
  nth_rewrite 0 [← add_zero a] at ia,
  rw ← iia at ia,
  rw ← add_assoc at ia,
  rw right_inv a at ia,
  rw zero_add at ia,
  have ia2 := right_inv a,
  rw iia at ia,
  rw ← ia at ia2,
  have := right_cancel ia2,
  symmetry,
  exact this,
end
lemma left_inv : ∀(a : R), (-a) + a = 0 :=
begin 
  intro a,
  have := right_inv (-a),
  rw inv_of_inv a at this,
  exact this,
end
lemma left_cancel : ∀{a b c: R}, c + a = c + b → a = b :=
begin
  intros a b c h,
  have start : 0 + a = a,
    exact zero_add a,
  have bruh := right_inv (-c),
  rw ← bruh at start,
  rw inv_of_inv c at start,
  rw add_assoc at start,
  rw h at start,
  rw ← add_assoc at start,
  rw left_inv c at start,
  rw zero_add at start,
  symmetry,
  exact start,
end
lemma add_comm : ∀ (a b : R), a + b = b + a :=
begin 
  intros a b,
  have one : (a + 1) * (b + 1) = b * a + b + a + 1,
  {
    rw mul_add,
    rw mul_comm,
    rw mul_add,
    rw mul_one,
    rw mul_one,
    rw ← add_assoc,
  },
  have two : (a + 1) * (b + 1) = a * b + a + b + 1,
  {
    rw mul_comm,
    rw mul_add,
    rw mul_comm,
    rw mul_add,
    rw mul_one,
    rw mul_one,
    rw ← add_assoc,
  },
  rw one at two,
  have := right_cancel two,
  rw mul_comm at this,
  rw add_assoc at this,
  rw add_assoc (a*b) a b at this,
  have final := left_cancel this,
  symmetry,
  exact final,
end 
end ring'