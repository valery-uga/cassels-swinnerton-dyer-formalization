import AllCharacteristics.InvariantQuotientOpenPullback
import AllCharacteristics.AffineSchemeActionQuotientMorphism
import AllCharacteristics.AffineSchemeActionOpenDescent
import AllCharacteristics.EquivariantOpenImage

/-!
# Open immersions between actual affine scheme action quotients

An equivariant open immersion descends to an open immersion between the
constructed quotients of the original affine schemes. Its quotient square
is Cartesian, with all maps retaining their original scheme meanings.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v

/-- The global-section spectrum map of an actual affine open immersion is
an open immersion. -/
theorem isOpenImmersion_Spec_appTop_of_affine_open
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (a : X ⟶ Y) [IsOpenImmersion a] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom a.appTop.hom)) := by
  have hn : X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom a.appTop.hom) =
      a ≫ Y.isoSpec.hom := Scheme.isoSpec_hom_naturality a
  have he : Spec.map (CommRingCat.ofHom a.appTop.hom) =
      X.isoSpec.inv ≫ a ≫ Y.isoSpec.hom := by
    rw [← hn, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

variable {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y]
variable (G : Type v) [Group G] [Finite G]
variable (ρX : G → (X ⟶ X)) (hX₁ : ρX 1 = 𝟙 X)
variable (hXcomp : ∀ g h : G, ρX (g * h) = ρX g ≫ ρX h)
variable (ρY : G → (Y ⟶ Y)) (hY₁ : ρY 1 = 𝟙 Y)
variable (hYcomp : ∀ g h : G, ρY (g * h) = ρY g ≫ ρY h)
variable (p : X ⟶ S) (hp : ∀ g : G, ρX g ≫ p = p)
variable (q : Y ⟶ S) (hq : ∀ g : G, ρY g ≫ q = q)
variable (a : X ⟶ Y) (ha : ∀ g : G, ρX g ≫ a = a ≫ ρY g)

/-- Equivariant open immersions of the original affine schemes descend to
actual open immersions of their constructed action quotients. -/
theorem isOpenImmersion_affineSchemeActionQuotientMorphism [IsOpenImmersion a] :
    IsOpenImmersion
      (affineSchemeActionQuotientMorphism G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha) := by
  let := schemeGlobalSectionAction G ρX hX₁ hXcomp
  let := schemeGlobalSectionAction G ρY hY₁ hYcomp
  let := p.appTop.hom.toAlgebra
  let := q.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρX hX₁ hXcomp p hp
  let : SMulCommClass G Γ(S, ⊤) Γ(Y, ⊤) := schemeGlobalSectionAction_smulComm G ρY hY₁ hYcomp q hq
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom a.appTop.hom)) :=
    isOpenImmersion_Spec_appTop_of_affine_open a
  exact isOpenImmersion_affineInvariantQuotientMorphism Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) G a.appTop.hom
    (fun g s ↦ (appTop_equivariant_of_scheme_equivariant ρX ρY a ha g s).symm)

/-- The actual descended map has the quotient image of the original map as its range. -/
theorem affineSchemeActionQuotientMorphism_range :
    Set.range (affineSchemeActionQuotientMorphism G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha) =
      (affineSchemeActionQuotientMap G ρY hY₁ hYcomp q hq) '' Set.range a := by
  have he (x : X) :
      affineSchemeActionQuotientMorphism G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha
          (affineSchemeActionQuotientMap G ρX hX₁ hXcomp p hp x) =
        affineSchemeActionQuotientMap G ρY hY₁ hYcomp q hq (a x) :=
    congrArg (fun m : X ⟶ affineSchemeActionQuotient G ρY hY₁ hYcomp q hq ↦ m x)
      (affineSchemeActionQuotientMorphism_square G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha)
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (affineSchemeActionQuotientMap G ρX hX₁ hXcomp p hp).surjective y
    exact ⟨_, ⟨x, rfl⟩, (he x).symm⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨affineSchemeActionQuotientMap G ρX hX₁ hXcomp p hp x, he x⟩

/-- The full inverse image of the descended quotient range is the original stable open. -/
theorem affineSchemeActionQuotientMorphism_preimage_range [IsOpenImmersion a] :
    (affineSchemeActionQuotientMap G ρY hY₁ hYcomp q hq) ⁻¹'
      Set.range (affineSchemeActionQuotientMorphism G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha) =
        Set.range a := by
  rw [affineSchemeActionQuotientMorphism_range]
  exact preimage_image_affineSchemeActionOpen G ρY hY₁ hYcomp q hq a.opensRange
    (equivariant_opensRange_preimage G ρY hY₁ hYcomp ρX a ha)

/-- The original affine open immersion is exactly the base change of the
constructed open immersion of action quotients. -/
theorem isPullback_affineSchemeActionQuotientMorphism [IsOpenImmersion a] :
    IsPullback a (affineSchemeActionQuotientMap G ρX hX₁ hXcomp p hp)
      (affineSchemeActionQuotientMap G ρY hY₁ hYcomp q hq)
      (affineSchemeActionQuotientMorphism G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha) := by
  have : IsOpenImmersion
      (affineSchemeActionQuotientMorphism G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha) :=
    isOpenImmersion_affineSchemeActionQuotientMorphism G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha
  apply (IsOpenImmersion.isPullback (affineSchemeActionQuotientMap G ρX hX₁ hXcomp p hp)
    a (affineSchemeActionQuotientMorphism G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha)
    (affineSchemeActionQuotientMap G ρY hY₁ hYcomp q hq)
    (affineSchemeActionQuotientMorphism_square G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha).symm ?_).flip
  apply SetLike.coe_injective
  change (affineSchemeActionQuotientMap G ρY hY₁ hYcomp q hq) ⁻¹'
    Set.range (affineSchemeActionQuotientMorphism G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha) =
      Set.range a
  rw [affineSchemeActionQuotientMorphism_range]
  exact preimage_image_affineSchemeActionOpen G ρY hY₁ hYcomp q hq a.opensRange
    (equivariant_opensRange_preimage G ρY hY₁ hYcomp ρX a ha)

end AllCharacteristics
