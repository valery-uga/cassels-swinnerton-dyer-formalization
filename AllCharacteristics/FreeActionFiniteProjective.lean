import AllCharacteristics.FreeActionGaloisCoordinates
import AllCharacteristics.InvariantOrbitTrace
import AllCharacteristics.FiniteDualGenerators

/-!
# Finite projectivity of an actual free finite-group invariant quotient

The coordinate identity and the orbit trace give a direct summand of a finite
free module over the actual invariant ring. No invertibility of the group
order or preexisting flatness of the quotient is assumed.
-/

namespace AllCharacteristics
universe u v
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (G : Type v) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- A finite group action with no nonidentity affine fixed locus makes the
original ring finite projective over its actual invariant subalgebra. -/
theorem finite_projective_fixedSubalgebra_of_free_action
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    Module.Finite (FixedPoints.subalgebra R B G) B ∧
      Module.Projective (FixedPoints.subalgebra R B G) B := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨n, a, b, hc⟩ := exists_freeAction_galois_coordinates R B G hfree
  let I := FixedPoints.subalgebra R B G
  let ℓ : Fin n → B →ₗ[I] I := fun i ↦
    (invariantOrbitTrace R B G).comp (LinearMap.mulLeft I (b i))
  apply finite_projective_of_dual_generators I B a ℓ
  intro x
  exact invariantOrbitTrace_dual_generators R B G a b hc x

end AllCharacteristics
