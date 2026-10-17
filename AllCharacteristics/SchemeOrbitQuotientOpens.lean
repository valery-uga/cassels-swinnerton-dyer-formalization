import AllCharacteristics.AffineSchemeActionOpenDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Stable open subschemes of an actual orbit quotient

A scheme morphism with the quotient topology and the proved orbit fibers
is open. Every stable open descends to an actual open subscheme, and its
restricted quotient square is Cartesian. These results can be applied to
the constructed full projective tuple quotient.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AllCharacteristics
universe u v
variable {X Y : Scheme.{u}} (G : Type v) (ρ : G → (X ⟶ X))
variable (q : X ⟶ Y) (hQ : Topology.IsQuotientMap q)
variable (hOrbit : ∀ x y : X, q x = q y ↔ ∃ g : G, ρ g x = y)

include hOrbit in
/-- The saturation under an actual orbit quotient is the union of all action preimages. -/
theorem schemeOrbitQuotient_saturation (W : Set X) :
    q ⁻¹' (q '' W) = ⋃ g : G, (ρ g) ⁻¹' W := by
  ext y
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨g, hg⟩ := (hOrbit y x).mp he.symm
    exact ⟨g, hg.symm ▸ hx⟩
  · rintro ⟨g, hg⟩
    exact ⟨ρ g y, hg, ((hOrbit y (ρ g y)).mpr ⟨g, rfl⟩).symm⟩

include hQ hOrbit in
/-- A scheme quotient with actual orbit fibers is an open map. -/
theorem isOpenMap_schemeOrbitQuotient : IsOpenMap q := by
  intro W hW
  apply hQ.isCoinducing.isOpen_preimage.mp
  rw [schemeOrbitQuotient_saturation G ρ q hOrbit]
  exact isOpen_iUnion (fun g ↦ hW.preimage (ρ g).continuous)

/-- The actual image open under the constructed orbit quotient. -/
def schemeOrbitQuotientOpen (U : X.Opens) : Y.Opens :=
  ⟨q '' (U : Set X), isOpenMap_schemeOrbitQuotient G ρ q hQ hOrbit _ U.isOpen⟩

variable (U : X.Opens) (hU : ∀ g : G, (ρ g) ⁻¹ᵁ U = U)

include hU in
/-- A stable open is exactly the full inverse image of its actual quotient image. -/
theorem schemeOrbitQuotientOpen_preimage : q ⁻¹ᵁ schemeOrbitQuotientOpen G ρ q hQ hOrbit U = U := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨g, hg⟩ := (hOrbit x y).mp he.symm
    have hm : x ∈ (ρ g) ⁻¹ᵁ U := show ρ g x ∈ U from hg.symm ▸ hy
    rw [hU g] at hm
    exact hm
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The actual restricted quotient morphism from a stable open to its image open. -/
noncomputable def schemeOrbitOpenQuotientMap :
    U.toScheme ⟶ (schemeOrbitQuotientOpen G ρ q hQ hOrbit U).toScheme :=
  IsOpenImmersion.lift (schemeOrbitQuotientOpen G ρ q hQ hOrbit U).ι (U.ι ≫ q) (by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨q x.val, ⟨x.val, x.property, rfl⟩⟩, rfl⟩)

/-- The restricted quotient morphism retains the two actual open inclusions. -/
theorem schemeOrbitOpenQuotientMap_ι :
    schemeOrbitOpenQuotientMap G ρ q hQ hOrbit U ≫
      (schemeOrbitQuotientOpen G ρ q hQ hOrbit U).ι = U.ι ≫ q :=
  IsOpenImmersion.lift_fac _ _ _

include hU in
/-- The stable-open quotient square is the actual base change of the original quotient. -/
theorem isPullback_schemeOrbitOpenQuotientMap :
    IsPullback U.ι (schemeOrbitOpenQuotientMap G ρ q hQ hOrbit U) q
      (schemeOrbitQuotientOpen G ρ q hQ hOrbit U).ι := by
  apply (IsOpenImmersion.isPullback (schemeOrbitOpenQuotientMap G ρ q hQ hOrbit U) U.ι
    (schemeOrbitQuotientOpen G ρ q hQ hOrbit U).ι q
    (schemeOrbitOpenQuotientMap_ι G ρ q hQ hOrbit U).symm ?_).flip
  simpa only [Scheme.Opens.opensRange_ι] using schemeOrbitQuotientOpen_preimage G ρ q hQ hOrbit U hU

/-- Every point of the actual image open has a point above it in the original open. -/
instance surjective_schemeOrbitOpenQuotientMap :
    Surjective (schemeOrbitOpenQuotientMap G ρ q hQ hOrbit U) := by
  constructor
  intro y
  obtain ⟨x, hx, he⟩ := y.property
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact (congrArg (fun m : U.toScheme ⟶ Y ↦ m ⟨x, hx⟩)
    (schemeOrbitOpenQuotientMap_ι G ρ q hQ hOrbit U)).trans he

include hU in
/-- Integral orbit quotients remain integral on the actual stable-open quotient. -/
theorem isIntegralHom_schemeOrbitOpenQuotientMap [IsIntegralHom q] :
    IsIntegralHom (schemeOrbitOpenQuotientMap G ρ q hQ hOrbit U) :=
  MorphismProperty.of_isPullback (P := @IsIntegralHom.{u})
    (isPullback_schemeOrbitOpenQuotientMap G ρ q hQ hOrbit U hU) inferInstance

include hU in
/-- Finite orbit quotients remain finite on the actual stable-open quotient. -/
theorem isFinite_schemeOrbitOpenQuotientMap [IsFinite q] :
    IsFinite (schemeOrbitOpenQuotientMap G ρ q hQ hOrbit U) :=
  MorphismProperty.of_isPullback (P := @IsFinite.{u})
    (isPullback_schemeOrbitOpenQuotientMap G ρ q hQ hOrbit U hU) inferInstance

end AllCharacteristics
