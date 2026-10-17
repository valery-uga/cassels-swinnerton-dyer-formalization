import PfaffianDescent.ThreeGeneratorKoszul

/-! # A Cartier-equation homotopy on the ambient point Koszul complex

If an ambient hypersurface equation is written as `f*a + g*b + h*c`,
multiplication by that equation is explicitly null-homotopic on the Koszul
complex for the point ideal `(f,g,h)`. These are algebraic identities over
any commutative ring, before sheafification or passage to Ext. In particular,
this file does not identify the global point pullback with a Laurent residue
and does not prove its nonvanishing.
-/

namespace PfaffianDescent

variable {R : Type*} [CommRing R]

/-- Wedge multiplication by the coefficients of a Cartier equation, in degree zero. -/
def pointGlobalTraceCartierHomotopyZero (a b c : R) : R →ₗ[R] R × R × R where
  toFun x := (a * x, b * x, c * x)
  map_add' x y := by ext <;> simp [mul_add]
  map_smul' r x := by ext <;> simp [mul_left_comm]

/-- Wedge multiplication by the equation coefficients in degree one,
with the orientation of `threeGeneratorMiddle`. -/
def pointGlobalTraceCartierHomotopyOne (a b c : R) :
    R × R × R →ₗ[R] R × R × R where
  toFun x := (a * x.2.1 - b * x.1,
    a * x.2.2 - c * x.1, b * x.2.2 - c * x.2.1)
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' r x := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring

/-- Wedge multiplication by the equation coefficients in degree two. -/
def pointGlobalTraceCartierHomotopyTwo (a b c : R) : R × R × R →ₗ[R] R where
  toFun x := c * x.1 - b * x.2.1 + a * x.2.2
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

/-- The degree-zero homotopy identity is exactly the Cartier equation. -/
theorem pointGlobalTraceCartierHomotopy_degreeZero (f g h a b c x : R) :
    threeGeneratorLast f g h (pointGlobalTraceCartierHomotopyZero a b c x) =
      (f * a + g * b + h * c) * x := by
  change f * (a * x) + g * (b * x) + h * (c * x) = _
  ring

/-- The degree-one homotopy identity, in the actual ambient Koszul orientation. -/
theorem pointGlobalTraceCartierHomotopy_degreeOne (f g h a b c : R)
    (x : R × R × R) :
    threeGeneratorMiddle f g h (pointGlobalTraceCartierHomotopyOne a b c x) +
      pointGlobalTraceCartierHomotopyZero a b c (threeGeneratorLast f g h x) =
        (f * a + g * b + h * c) • x := by
  ext <;>
    simp only [threeGeneratorMiddle, threeGeneratorLast,
      pointGlobalTraceCartierHomotopyZero, pointGlobalTraceCartierHomotopyOne,
      LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- The degree-two homotopy identity. -/
theorem pointGlobalTraceCartierHomotopy_degreeTwo (f g h a b c : R)
    (x : R × R × R) :
    threeGeneratorFirst f g h (pointGlobalTraceCartierHomotopyTwo a b c x) +
      pointGlobalTraceCartierHomotopyOne a b c (threeGeneratorMiddle f g h x) =
        (f * a + g * b + h * c) • x := by
  ext <;>
    simp only [threeGeneratorFirst, threeGeneratorMiddle,
      pointGlobalTraceCartierHomotopyOne, pointGlobalTraceCartierHomotopyTwo,
      LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- The degree-three homotopy identity. -/
theorem pointGlobalTraceCartierHomotopy_degreeThree (f g h a b c x : R) :
    pointGlobalTraceCartierHomotopyTwo a b c (threeGeneratorFirst f g h x) =
      (f * a + g * b + h * c) * x := by
  change c * (h * x) - b * (-g * x) + a * (f * x) = _
  ring

end PfaffianDescent
