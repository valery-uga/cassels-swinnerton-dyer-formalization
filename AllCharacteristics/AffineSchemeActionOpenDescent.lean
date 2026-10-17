import AllCharacteristics.AffineSchemeActionOrbits

/-!
# Open sets of the quotient of the original affine scheme action

The actual finite-group quotient map is both a topological quotient map and
an open map. Its saturation of a subset is the union of its group translates.
A stable open therefore descends to an actual quotient open whose full
inverse image is exactly the original open subscheme.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AllCharacteristics
universe u v
variable {X S : Scheme.{u}} [IsAffine X] (G : Type v) [Group G] [Finite G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
variable (f : X ⟶ S) (hf : ∀ g : G, ρ g ≫ f = f)

/-- The original affine-scheme quotient map is a topological quotient map. -/
theorem isQuotientMap_affineSchemeActionQuotientMap :
    Topology.IsQuotientMap (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) :=
  (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf).isClosedMap.isQuotientMap
    (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf).continuous
    (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf).surjective

/-- Saturation of a subset by the actual quotient map is the union of its group translates. -/
theorem affineSchemeActionQuotientMap_saturation (W : Set X) :
    (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) ⁻¹'
      ((affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) '' W) =
        ⋃ g : G, (ρ g) ⁻¹' W := by
  ext y
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨g, hg⟩ := (affineSchemeActionQuotientMap_eq_iff_orbit G ρ h₁ hcomp f hf y x).mp he.symm
    exact ⟨g, hg.symm ▸ hx⟩
  · rintro ⟨g, hg⟩
    exact ⟨ρ g y, hg,
      ((affineSchemeActionQuotientMap_eq_iff_orbit G ρ h₁ hcomp f hf y (ρ g y)).mpr ⟨g, rfl⟩).symm⟩

/-- The actual quotient map of a finite scheme action is open. -/
theorem isOpenMap_affineSchemeActionQuotientMap :
    IsOpenMap (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) := by
  intro W hW
  apply (isQuotientMap_affineSchemeActionQuotientMap G ρ h₁ hcomp f hf).isCoinducing.isOpen_preimage.mp
  rw [affineSchemeActionQuotientMap_saturation]
  exact isOpen_iUnion (fun g ↦ hW.preimage (ρ g).continuous)

/-- The actual image open of an open subscheme under the constructed quotient. -/
def affineSchemeActionQuotientOpen (W : X.Opens) :
    (affineSchemeActionQuotient G ρ h₁ hcomp f hf).Opens :=
  ⟨(affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) '' (W : Set X),
    isOpenMap_affineSchemeActionQuotientMap G ρ h₁ hcomp f hf _ W.isOpen⟩

/-- A stable open is the full inverse image of its actual quotient image. -/
theorem preimage_image_affineSchemeActionOpen (W : X.Opens)
    (hW : ∀ g : G, (ρ g) ⁻¹ᵁ W = W) :
    (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) ⁻¹'
      ((affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) '' (W : Set X)) = W := by
  rw [affineSchemeActionQuotientMap_saturation]
  have he (g : G) : (ρ g) ⁻¹' (W : Set X) = W := congrArg (fun V : X.Opens ↦ (V : Set X)) (hW g)
  simp only [he, Set.iUnion_const]

/-- Pullback of the actual descended quotient open recovers the original stable open. -/
theorem affineSchemeActionQuotientOpen_preimage (W : X.Opens)
    (hW : ∀ g : G, (ρ g) ⁻¹ᵁ W = W) :
    (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) ⁻¹ᵁ
      affineSchemeActionQuotientOpen G ρ h₁ hcomp f hf W = W := by
  apply SetLike.coe_injective
  exact preimage_image_affineSchemeActionOpen G ρ h₁ hcomp f hf W hW

end AllCharacteristics
