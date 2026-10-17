import AllCharacteristics.AffineInvariantQuotient

/-!
# Factorization through an actual invariant spectrum

An invariant ring map factors uniquely through the fixed subalgebra. Applying
`Spec` gives the actual affine quotient factorization. The quotient map is
invariant under every original group element. No division by the group order
or characteristic restriction enters these constructions.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (G : Type v) [Group G] [MulSemiringAction G A] [SMulCommClass G R A]
variable {B : Type u} [CommRing B] (φ : B →+* A) (hφ : ∀ b : B, ∀ g : G, g • φ b = φ b)

/-- The actual factor of an invariant ring map through the invariant subalgebra. -/
def invariantRingFactor : B →+* FixedPoints.subalgebra R A G where
  toFun b := ⟨φ b, hφ b⟩
  map_zero' := Subtype.ext φ.map_zero
  map_one' := Subtype.ext φ.map_one
  map_add' x y := Subtype.ext (φ.map_add x y)
  map_mul' x y := Subtype.ext (φ.map_mul x y)

/-- Inclusion of the invariant factor recovers the original ring map exactly. -/
theorem invariantRingFactor_comp :
    (algebraMap (FixedPoints.subalgebra R A G) A).comp (invariantRingFactor R A G φ hφ) = φ := by
  apply RingHom.ext
  intro b
  rfl

/-- The factor through the invariant subalgebra is unique. -/
theorem invariantRingFactor_unique (ψ : B →+* FixedPoints.subalgebra R A G)
    (hψ : (algebraMap (FixedPoints.subalgebra R A G) A).comp ψ = φ) :
    ψ = invariantRingFactor R A G φ hφ := by
  apply RingHom.ext
  intro b
  apply Subtype.ext
  exact congrArg (fun h : B →+* A ↦ h b) hψ

/-- An invariant ring map gives an actual morphism out of the invariant spectrum. -/
noncomputable def affineInvariantFactor : affineInvariantQuotient R A G ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (invariantRingFactor R A G φ hφ))

/-- The resulting scheme morphism factors the original affine morphism. -/
theorem affineInvariantFactor_comp :
    affineInvariantQuotientMap R A G ≫ affineInvariantFactor R A G φ hφ =
      Spec.map (CommRingCat.ofHom φ) := by
  change Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R A G) A)) ≫
    Spec.map (CommRingCat.ofHom (invariantRingFactor R A G φ hφ)) = _
  rw [← Spec.map_comp]
  exact congrArg (fun h : B →+* A ↦ Spec.map (CommRingCat.ofHom h))
    (invariantRingFactor_comp R A G φ hφ)

/-- The factorization is unique among all morphisms to the given affine target. -/
theorem affineInvariantFactor_unique (ψ : affineInvariantQuotient R A G ⟶ Spec (.of B))
    (hψ : affineInvariantQuotientMap R A G ≫ ψ = Spec.map (CommRingCat.ofHom φ)) :
    ψ = affineInvariantFactor R A G φ hφ := by
  let ψRing : CommRingCat.of B ⟶ CommRingCat.of (FixedPoints.subalgebra R A G) := Spec.preimage ψ
  have hmap : Spec.map ψRing = ψ := Spec.map_preimage ψ
  have hcomm : ψRing ≫ CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R A G) A) =
      CommRingCat.ofHom φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hmap]
    exact hψ
  have he := invariantRingFactor_unique R A G φ hφ ψRing.hom
    (congrArg CommRingCat.Hom.hom hcomm)
  rw [← hmap]
  exact congrArg (fun h : B →+* FixedPoints.subalgebra R A G ↦ Spec.map (CommRingCat.ofHom h)) he

include hφ in
/-- The invariant spectrum has the exact affine-target quotient factorization property. -/
theorem existsUnique_affineInvariantFactor :
    ∃! ψ : affineInvariantQuotient R A G ⟶ Spec (.of B),
      affineInvariantQuotientMap R A G ≫ ψ = Spec.map (CommRingCat.ofHom φ) :=
  ⟨affineInvariantFactor R A G φ hφ, affineInvariantFactor_comp R A G φ hφ,
    fun ψ hψ ↦ affineInvariantFactor_unique R A G φ hφ ψ hψ⟩

/-- The canonical quotient morphism is invariant under every element of the original group. -/
theorem affineInvariantQuotientMap_invariant (g : G) :
    Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g)) ≫
      affineInvariantQuotientMap R A G = affineInvariantQuotientMap R A G := by
  have he : (MulSemiringAction.toRingHom G A g).comp
      (algebraMap (FixedPoints.subalgebra R A G) A) =
        algebraMap (FixedPoints.subalgebra R A G) A := by
    apply RingHom.ext
    intro a
    exact a.property g
  change Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R A G) A)) = _
  rw [← Spec.map_comp]
  exact congrArg (fun h : FixedPoints.subalgebra R A G →+* A ↦ Spec.map (CommRingCat.ofHom h)) he

end AllCharacteristics
