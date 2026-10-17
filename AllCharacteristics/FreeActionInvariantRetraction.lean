import AllCharacteristics.FreeActionTraceOne

/-!
# A linear retraction onto the actual invariant ring of a free action

A trace-one element gives an invariant-linear retraction of the original
invariant inclusion. Restricting scalars shows that flatness over the original
coefficient ring descends, without dividing by the group order.
-/

namespace AllCharacteristics
universe u v
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (G : Type v) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G R B]
variable (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤)

/-- Multiplication by a proved trace-one element followed by the actual orbit
trace gives a linear map to the original invariant subalgebra. -/
noncomputable def invariantOrbitTraceRetraction :
    B →ₗ[FixedPoints.subalgebra R B G] FixedPoints.subalgebra R B G where
  toFun b := invariantOrbitTrace R B G ((exists_invariantOrbitTrace_eq_one R B G hfree).choose * b)
  map_add' a b := by rw [mul_add, map_add]
  map_smul' a b := by rw [mul_smul_comm, map_smul]; rfl

/-- The trace retraction is the identity on the actual invariant inclusion. -/
theorem invariantOrbitTraceRetraction_algebraMap (a : FixedPoints.subalgebra R B G) :
    invariantOrbitTraceRetraction R B G hfree (algebraMap (FixedPoints.subalgebra R B G) B a) = a := by
  let b := (exists_invariantOrbitTrace_eq_one R B G hfree).choose
  have hb : invariantOrbitTrace R B G b = 1 :=
    (exists_invariantOrbitTrace_eq_one R B G hfree).choose_spec
  change invariantOrbitTrace R B G (b * algebraMap (FixedPoints.subalgebra R B G) B a) = a
  rw [mul_comm, ← Algebra.smul_def, map_smul, hb, smul_eq_mul, mul_one]

include hfree in
/-- The actual invariant ring of a free finite-group action inherits
flatness over any original coefficient ring from the original algebra. -/
theorem flat_fixedSubalgebra_of_free_action [Module.Flat R B] :
    Module.Flat R (FixedPoints.subalgebra R B G) := by
  let I := FixedPoints.subalgebra R B G
  let i : I →ₗ[R] B := (Algebra.linearMap I B).restrictScalars R
  let r : B →ₗ[R] I := (invariantOrbitTraceRetraction R B G hfree).restrictScalars R
  apply Module.Flat.of_retract i r
  apply LinearMap.ext
  intro a
  exact invariantOrbitTraceRetraction_algebraMap R B G hfree a

end AllCharacteristics
