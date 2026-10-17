import AllCharacteristics.InvariantSubalgebraMaps

/-!
# Functorial maps of invariant rings and affine quotients

Every equivariant ring homomorphism induces the actual map of invariant
rings and the contravariant morphism of their quotient spectra. Identity,
composition, and compatibility with the original quotient morphisms are
proved for these constructed maps.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : Type v) [Group G]
variable [MulSemiringAction G A] [MulSemiringAction G B]
variable [SMulCommClass G R A] [SMulCommClass G R B]
variable (φ : A →+* B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)

/-- The actual invariant-ring homomorphism induced by an arbitrary equivariant ring map. -/
def equivariantInvariantMap : FixedPoints.subalgebra R A G →+* FixedPoints.subalgebra R B G :=
  invariantRingFactor R B G
    (φ.comp (algebraMap (FixedPoints.subalgebra R A G) A)) (fun a g ↦ by
      change g • φ a.val = φ a.val
      rw [← hφ, a.property g])

/-- The induced invariant homomorphism has the original underlying ring map. -/
theorem equivariantInvariantMap_apply (a : FixedPoints.subalgebra R A G) :
    (equivariantInvariantMap R A B G φ hφ a).val = φ a.val := rfl

/-- Inclusion of invariants commutes with the actual induced map. -/
theorem equivariantInvariantMap_inclusion :
    (algebraMap (FixedPoints.subalgebra R B G) B).comp (equivariantInvariantMap R A B G φ hφ) =
      φ.comp (algebraMap (FixedPoints.subalgebra R A G) A) := rfl

/-- The identity ring homomorphism induces the identity on the invariant ring. -/
theorem equivariantInvariantMap_id :
    equivariantInvariantMap R A A G (RingHom.id A) (fun _ _ ↦ rfl) =
      RingHom.id (FixedPoints.subalgebra R A G) := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  rfl

/-- The invariant-ring construction respects composition of equivariant maps. -/
theorem equivariantInvariantMap_comp {C : Type u} [CommRing C] [Algebra R C]
    [MulSemiringAction G C] [SMulCommClass G R C]
    (ψ : B →+* C) (hψ : ∀ (g : G) (b : B), ψ (g • b) = g • ψ b) :
    equivariantInvariantMap R A C G (ψ.comp φ)
      (fun g a ↦ by change ψ (φ (g • a)) = g • ψ (φ a); rw [hφ, hψ]) =
        (equivariantInvariantMap R B C G ψ hψ).comp (equivariantInvariantMap R A B G φ hφ) := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  rfl

/-- The actual contravariant morphism of affine invariant quotient schemes. -/
noncomputable def affineInvariantQuotientMorphism :
    affineInvariantQuotient R B G ⟶ affineInvariantQuotient R A G :=
  Spec.map (CommRingCat.ofHom (equivariantInvariantMap R A B G φ hφ))

/-- The induced quotient morphism forms a commutative square with the original ring map. -/
theorem affineInvariantQuotientMorphism_square :
    affineInvariantQuotientMap R B G ≫ affineInvariantQuotientMorphism R A B G φ hφ =
      Spec.map (CommRingCat.ofHom φ) ≫ affineInvariantQuotientMap R A G := by
  change Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R B G) B)) ≫
    Spec.map (CommRingCat.ofHom (equivariantInvariantMap R A B G φ hφ)) =
      Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R A G) A))
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The identity map induces the identity on the actual affine quotient scheme. -/
theorem affineInvariantQuotientMorphism_id :
    affineInvariantQuotientMorphism R A A G (RingHom.id A) (fun _ _ ↦ rfl) =
      𝟙 (affineInvariantQuotient R A G) := by
  unfold affineInvariantQuotientMorphism
  rw [equivariantInvariantMap_id]
  exact Spec.map_id _

/-- Composition of equivariant ring maps induces actual composition of quotient morphisms. -/
theorem affineInvariantQuotientMorphism_comp {C : Type u} [CommRing C] [Algebra R C]
    [MulSemiringAction G C] [SMulCommClass G R C]
    (ψ : B →+* C) (hψ : ∀ (g : G) (b : B), ψ (g • b) = g • ψ b) :
    affineInvariantQuotientMorphism R A C G (ψ.comp φ)
      (fun g a ↦ by change ψ (φ (g • a)) = g • ψ (φ a); rw [hφ, hψ]) =
        affineInvariantQuotientMorphism R B C G ψ hψ ≫
          affineInvariantQuotientMorphism R A B G φ hφ := by
  unfold affineInvariantQuotientMorphism
  rw [equivariantInvariantMap_comp R A B G φ hφ ψ hψ]
  exact Spec.map_comp (CommRingCat.ofHom (equivariantInvariantMap R A B G φ hφ))
    (CommRingCat.ofHom (equivariantInvariantMap R B C G ψ hψ))

end AllCharacteristics
