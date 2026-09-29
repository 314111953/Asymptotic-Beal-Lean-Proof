import Mathlib

/-!
Algebra behind the proposed Pythagorean-theorem rewrite.

Lean's `^` here has natural-number exponents.  Thus we express the
``x / 2`` notation by assuming the original exponents are even:
`x = 2 * u`, `y = 2 * v`, and `z = 2 * w`.
-/

open Real

/-! `A^(2u) + B^(2v) = C^(2w)` is precisely a Pythagorean equation. -/
theorem pythagorean_rewrite
    (A B C u v w : ℕ)
    (h : A ^ (2 * u) + B ^ (2 * v) = C ^ (2 * w)) :
    (A ^ u) ^ 2 + (B ^ v) ^ 2 = (C ^ w) ^ 2 := by
  simpa [Nat.mul_comm, Nat.pow_mul] using h

/-!
If the acute-angle construction gives
`A^u / C^w = sin θ`, then squaring it gives the claimed formula.
The positivity of `C` makes the displayed quotient geometrically meaningful;
the algebraic conclusion itself follows from `hsin`.
-/
theorem pythagorean_sine_square
    (A B C : ℕ) (u v w : ℕ) (θ : ℝ)
    (_hC : 0 < C)
    (_hpyth : ((A : ℝ) ^ u) ^ 2 + ((B : ℝ) ^ v) ^ 2 = ((C : ℝ) ^ w) ^ 2)
    (hsin : (A : ℝ) ^ u / (C : ℝ) ^ w = sin θ) :
    (A : ℝ) ^ (2 * u) / (C : ℝ) ^ (2 * w) = (sin θ) ^ 2 := by
  calc
    (A : ℝ) ^ (2 * u) / (C : ℝ) ^ (2 * w) =
        ((A : ℝ) ^ u / (C : ℝ) ^ w) ^ 2 := by
      rw [show 2 * u = u * 2 by omega, pow_mul]
      rw [show 2 * w = w * 2 by omega, pow_mul]
      rw [div_pow]
    _ = (sin θ) ^ 2 := by rw [hsin]

/-!
This is the user's notation after setting `x = 2u` and `z = 2w`:
`A^x / C^z = sin(theta)^2`.
-/
theorem pythagorean_sine_square_even_exponents
    (A B C u v w : ℕ) (θ : ℝ)
    (hC : 0 < C)
    (hpyth : ((A : ℝ) ^ u) ^ 2 + ((B : ℝ) ^ v) ^ 2 = ((C : ℝ) ^ w) ^ 2)
    (hsin : (A : ℝ) ^ u / (C : ℝ) ^ w = sin θ) :
    (A : ℝ) ^ (2 * u) / (C : ℝ) ^ (2 * w) = (sin θ) ^ 2 :=
  pythagorean_sine_square A B C u v w θ hC hpyth hsin

/-! The corresponding cosine equation, using `B^v / C^w = cos θ`. -/
theorem pythagorean_cosine_square
    (A B C : ℕ) (u v w : ℕ) (θ : ℝ)
    (_hC : 0 < C)
    (_hpyth : ((A : ℝ) ^ u) ^ 2 + ((B : ℝ) ^ v) ^ 2 = ((C : ℝ) ^ w) ^ 2)
    (hcos : (B : ℝ) ^ v / (C : ℝ) ^ w = cos θ) :
    (B : ℝ) ^ (2 * v) / (C : ℝ) ^ (2 * w) = (cos θ) ^ 2 := by
  calc
    (B : ℝ) ^ (2 * v) / (C : ℝ) ^ (2 * w) =
        ((B : ℝ) ^ v / (C : ℝ) ^ w) ^ 2 := by
      rw [show 2 * v = v * 2 by omega, pow_mul]
      rw [show 2 * w = w * 2 by omega, pow_mul]
      rw [div_pow]
    _ = (cos θ) ^ 2 := by rw [hcos]

/-!
The next two results record the *root* and *asymptotic* parts of the
argument.  Here exponents are real exponents (`Real.rpow`), so `x / z`
really denotes division rather than natural-number quotient.

The root identity is supplied as `hroot`: deriving it from the preceding
equation needs the usual positive-base laws for real powers.  The conclusion
of an asymptotic argument is a limit, not an equality at any finite index.
-/
theorem root_equals_C_of_factor_one
    (A C θ x z : ℝ)
    (hroot : A ^ (x / z) = C * (sin θ) ^ (2 / z))
    (hfactor : (sin θ) ^ (2 / z) = 1) :
    A ^ (x / z) = C := by
  rw [hroot, hfactor, mul_one]

/-!
For sequences `x n` and `z n`, this is the rigorous replacement for
“as `x` and `z` tend to infinity, `A^(x/z) = C`”.  It concludes that the
left-hand side tends to `C`, once the sine factor tends to `1`.
-/
theorem root_tends_to_C
    (A C θ : ℝ) (x z : ℕ → ℝ)
    (hroot : ∀ n, A ^ (x n / z n) = C * (sin θ) ^ (2 / z n))
    (hfactor : Filter.Tendsto (fun n => (sin θ) ^ (2 / z n)) Filter.atTop
      (nhds 1)) :
    Filter.Tendsto (fun n => A ^ (x n / z n)) Filter.atTop (nhds C) := by
  have hconst : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) :=
    tendsto_const_nhds
  have hmul := hconst.mul hfactor
  have hmul' : Filter.Tendsto (fun n => C * (sin θ) ^ (2 / z n))
      Filter.atTop (nhds C) := by
    simpa using hmul
  simpa only [hroot] using hmul'

/-! The cosine counterpart of `root_tends_to_C`. -/
theorem cosine_root_tends_to_C
    (B C θ : ℝ) (y z : ℕ → ℝ)
    (hroot : ∀ n, B ^ (y n / z n) = C * (cos θ) ^ (2 / z n))
    (hfactor : Filter.Tendsto (fun n => (cos θ) ^ (2 / z n)) Filter.atTop
      (nhds 1)) :
    Filter.Tendsto (fun n => B ^ (y n / z n)) Filter.atTop (nhds C) := by
  have hconst : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) :=
    tendsto_const_nhds
  have hmul := hconst.mul hfactor
  have hmul' : Filter.Tendsto (fun n => C * (cos θ) ^ (2 / z n))
      Filter.atTop (nhds C) := by
    simpa using hmul
  simpa only [hroot] using hmul'

/-!
Integer-base special cases of an *exact* equality `A^(x/z) = C`.

They are not an exhaustive classification: a reduced rational ratio `a / b`
can occur whenever `A = D^b` and `C = D^a`.  In particular, tending to
infinity does not by itself force the ratio to be an integer or its inverse.
-/
theorem integer_ratio_case
    (A C D m : ℕ)
    (hA : A = D) (hC : C = D ^ m) :
    A ^ m = C := by
  rw [hA, hC]

theorem reciprocal_integer_ratio_case
    (A C D m : ℕ)
    (hA : A = D ^ m) (hC : C = D) :
    A = C ^ m := by
  rw [hA, hC]

/-!
If the common base is itself a prime power `p^n`, the reciprocal-ratio case
has the form `A = p^(m*n)` (equivalently `p^(n*m)`).
-/
theorem reciprocal_ratio_prime_power_case (p m n : ℕ) :
    (p ^ n) ^ m = p ^ (m * n) := by
  simpa [Nat.mul_comm] using (pow_mul p n m).symm

/-!
The same two useful cases for the cosine side.  They instantiate the generic
results above with `B` in place of `A`.  They are sufficient cases, not an
exhaustive classification of possible ratios `y / z`.
-/
theorem cosine_integer_ratio_case
    (B C D r : ℕ)
    (hB : B = D) (hC : C = D ^ r) :
    B ^ r = C :=
  integer_ratio_case B C D r hB hC

theorem cosine_reciprocal_integer_ratio_case
    (B C D r : ℕ)
    (hB : B = D ^ r) (hC : C = D) :
    B = C ^ r :=
  reciprocal_integer_ratio_case B C D r hB hC

/-! If `D = q^s`, then the previous case has `B = q^(r*s)` and `C = q^s`. -/
theorem cosine_reciprocal_prime_power_case (q r s : ℕ) :
    (q ^ s) ^ r = q ^ (r * s) :=
  reciprocal_ratio_prime_power_case q r s
