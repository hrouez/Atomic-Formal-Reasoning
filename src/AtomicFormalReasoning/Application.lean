import AtomicFormalReasoning.ComplexIdentities
import Mathlib.Data.Complex.Basic
open ComplexConjugate
open Complex



theorem application_1 (z : ℂ) :
  z * conj z +  (z + conj z) + I * (z - conj z) = ((z.re^2 + z.im^2 + 2 * z.re - 2 * z.im : ℝ) : ℂ) :=

  calc

  z * conj z +  (z + conj z) + I * (z - conj z)

  = ((z.re^2 + z.im^2 : ℝ) : ℂ) +  ((2 * z.re : ℝ) : ℂ) + I * ((2 * z.im : ℝ) * I) := by rw [mul_conj_1,add_conj_1,sub_conj_1]

    _ =  ((z.re^2 + z.im^2 : ℝ) : ℂ) + ((2 * z.re : ℝ): ℂ)  + (I * ((2 * z.im : ℝ) : ℂ)  * I) := by rw [mul_assoc, mul_comm I]

    _ =  ((z.re^2 + z.im^2 : ℝ) : ℂ) + ((2 * z.re : ℝ): ℂ)  + (((2 * z.im : ℝ) : ℂ) * I * I) := by rw [mul_assoc, mul_comm I]

    _ =  ((z.re^2 + z.im^2 : ℝ) : ℂ) + ((2 * z.re : ℝ): ℂ)  + (((2 * z.im : ℝ) : ℂ) * (I * I)) := by rw [mul_assoc, mul_comm I]

    _ = ((z.re^2 + z.im^2 : ℝ) : ℂ) + ((2 * z.re : ℝ) : ℂ) + (((2 * z.im : ℝ) : ℂ) * (-1 : ℂ )):= by rw [I_mul_I]

    _ = ((z.re^2 + z.im^2 : ℝ) : ℂ) + ((2 * z.re : ℝ) : ℂ) + ((2 * z.im : ℝ) : ℂ) * ((-1 : ℝ) : ℂ) := by

      rw [Complex.ofReal_neg , Complex.ofReal_one]

    _ = ((z.re^2 + z.im^2 : ℝ) : ℂ) + ((2 * z.re : ℝ) : ℂ) + ((2 * z.im * -1 : ℝ) : ℂ) :=

      by rw [← Complex.ofReal_mul ,mul_assoc , mul_neg ]

    _ =((z.re^2 + z.im^2 : ℝ) : ℂ) + ((2 * z.re : ℝ) : ℂ) + ( (2 * (z.im * -1 ) : ℝ) : ℂ) :=

      by rw [ mul_assoc , mul_neg ]

    _ =((z.re^2 + z.im^2 : ℝ) : ℂ) + ((2 * z.re : ℝ) : ℂ) + ( (2 * (-z.im ) : ℝ) : ℂ) :=

      by rw [mul_neg ,mul_one]

    _ = ((z.re^2 + z.im^2 : ℝ) : ℂ) + ((2 * z.re : ℝ) : ℂ) + ((-(2 * z.im ) : ℝ) : ℂ) :=

      by rw [neg_mul_eq_mul_neg ]

    _ = ((z.re^2 + z.im^2 : ℝ) : ℂ) + ((2 * z.re : ℝ) : ℂ) + (-( 2 * z.im  : ℝ) : ℂ) :=

      by rw [Complex.ofReal_neg]

    _ = ((z.re^2 + z.im^2 : ℝ) : ℂ) + ((2 * z.re : ℝ) : ℂ) - (( 2 * z.im  : ℝ) : ℂ) :=

      by rw [sub_eq_add_neg]

    _ = ((z.re^2 + z.im^2 + 2 * z.re - 2 * z.im : ℝ) : ℂ) :=

      by rw [← Complex.ofReal_add, ← Complex.ofReal_sub]
