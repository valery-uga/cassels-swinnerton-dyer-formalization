import AllCharacteristics.AffineInvariantFactorization
import AllCharacteristics.LocalizedGroupAction

/-!
# Maps and units in invariant subalgebras

Equivariant algebra maps induce actual maps between fixed subalgebras.
Compatibility with a common coefficient ring passes through algebra towers.
An invariant element is a unit in the invariant subalgebra exactly when it is
a unit in the original ring, because its inverse is invariant as well.
-/

namespace AllCharacteristics
universe u v
section Tower
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable (G : Type v) [Group G] [MulSemiringAction G A] [MulSemiringAction G B]
variable [SMulCommClass G R A] [SMulDistribClass G A B]

include A in
/-- Equivariance of an algebra tower preserves commutation with its original scalar action. -/
theorem smulCommClass_of_equivariant_algebra_tower : SMulCommClass G R B := by
  constructor
  intro g r b
  simp only [Algebra.smul_def]
  rw [smul_mul', IsScalarTower.algebraMap_apply R A B,
    ← algebraMap.coe_smul' g (algebraMap R A r) B, smul_algebraMap]

variable [SMulCommClass G R B]

/-- The actual ring map induced between the two invariant subalgebras. -/
def equivariantFixedSubalgebraMap :
    FixedPoints.subalgebra R A G →+* FixedPoints.subalgebra R B G :=
  invariantRingFactor R B G
    ((algebraMap A B).comp (algebraMap (FixedPoints.subalgebra R A G) A))
    (fun a g ↦ by
      change g • algebraMap A B a.val = algebraMap A B a.val
      rw [← algebraMap.coe_smul' g a.val B, a.property g])

omit [IsScalarTower R A B] in
/-- The induced invariant map has the original underlying coefficient map. -/
theorem equivariantFixedSubalgebraMap_apply (a : FixedPoints.subalgebra R A G) :
    (equivariantFixedSubalgebraMap R A B G a).val = algebraMap A B a.val := rfl

omit [IsScalarTower R A B] in
/-- Inclusion into the original target ring commutes with the induced invariant map. -/
theorem equivariantFixedSubalgebraMap_comp :
    (algebraMap (FixedPoints.subalgebra R B G) B).comp (equivariantFixedSubalgebraMap R A B G) =
      (algebraMap A B).comp (algebraMap (FixedPoints.subalgebra R A G) A) := by
  apply RingHom.ext
  intro a
  rfl

/-- The algebra structure on target invariants induced by the actual equivariant map. -/
@[instance_reducible]
def equivariantFixedSubalgebraAlgebra :
    Algebra (FixedPoints.subalgebra R A G) (FixedPoints.subalgebra R B G) :=
  (equivariantFixedSubalgebraMap R A B G).toAlgebra

end Tower

section Units
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (G : Type v) [Group G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- An invariant element is invertible in the invariant subalgebra exactly
when it is invertible in the original ring. -/
theorem isUnit_fixedSubalgebra_iff (b : FixedPoints.subalgebra R B G) :
    IsUnit b ↔ IsUnit b.val := by
  constructor
  · intro h
    exact h.map (algebraMap (FixedPoints.subalgebra R B G) B)
  · rintro ⟨u, hu⟩
    have hf (g : G) : g • (u : B) = (u : B) := by
      rw [hu]
      exact b.property g
    have hi (g : G) : g • ((u⁻¹ : Bˣ) : B) = ((u⁻¹ : Bˣ) : B) := by
      apply u.isUnit.mul_left_cancel
      calc
        (u : B) * (g • ((u⁻¹ : Bˣ) : B)) =
            (g • (u : B)) * (g • ((u⁻¹ : Bˣ) : B)) := by rw [hf g]
        _ = g • ((u : B) * ((u⁻¹ : Bˣ) : B)) := (smul_mul' _ _ _).symm
        _ = 1 := by rw [u.mul_inv, smul_one]
        _ = (u : B) * ((u⁻¹ : Bˣ) : B) := u.mul_inv.symm
    refine ⟨⟨b, ⟨((u⁻¹ : Bˣ) : B), hi⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      change b.val * ((u⁻¹ : Bˣ) : B) = 1
      rw [← hu, u.mul_inv]
    · apply Subtype.ext
      change ((u⁻¹ : Bˣ) : B) * b.val = 1
      rw [← hu, u.inv_mul]

end Units
end AllCharacteristics
