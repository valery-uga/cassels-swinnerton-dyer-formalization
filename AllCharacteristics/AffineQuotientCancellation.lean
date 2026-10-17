import AllCharacteristics.AffineSchemeActionQuotient

/-!
# Cancellation of quotient maps against affine targets

The invariant-ring inclusion is injective. Consequently, two maps from the
actual quotient to an affine scheme agree whenever they agree after the
original quotient map. This gives the uniqueness needed for compatible
quotient-chart maps without assuming a global categorical quotient theorem.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
section InvariantRings
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (G : Type v) [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

/-- Quotient maps cancel against morphisms to an actual affine spectrum. -/
theorem affineInvariantQuotientMap_cancel_spec {B : Type u} [CommRing B]
    {a b : affineInvariantQuotient R A G ⟶ Spec (.of B)}
    (h : affineInvariantQuotientMap R A G ≫ a = affineInvariantQuotientMap R A G ≫ b) : a = b := by
  let aR : CommRingCat.of B ⟶ CommRingCat.of (FixedPoints.subalgebra R A G) := Spec.preimage a
  let bR : CommRingCat.of B ⟶ CommRingCat.of (FixedPoints.subalgebra R A G) := Spec.preimage b
  have he : aR ≫ CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R A G) A) =
      bR ≫ CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra R A G) A) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    have ha : Spec.map aR = a := Spec.map_preimage a
    have hb : Spec.map bR = b := Spec.map_preimage b
    rw [ha, hb]
    exact h
  have hr : aR = bR := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun m : CommRingCat.of B ⟶ CommRingCat.of A ↦ m.hom x) he
  exact (Spec.map_preimage a).symm.trans
    ((congrArg (fun m ↦ Spec.map m) hr).trans (Spec.map_preimage b))

/-- Quotient maps cancel against morphisms to any actual affine scheme. -/
theorem affineInvariantQuotientMap_cancel {T : Scheme.{u}} [IsAffine T]
    {a b : affineInvariantQuotient R A G ⟶ T}
    (h : affineInvariantQuotientMap R A G ≫ a = affineInvariantQuotientMap R A G ≫ b) : a = b := by
  apply (cancel_mono T.isoSpec.hom).mp
  apply affineInvariantQuotientMap_cancel_spec R A G
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m ↦ m ≫ T.isoSpec.hom) h).trans (Category.assoc _ _ _))

end InvariantRings

/-- The quotient map from the original affine scheme has the same affine-target cancellation. -/
theorem affineSchemeActionQuotientMap_cancel {X S T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (G : Type v) [Group G] (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
    (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
    (f : X ⟶ S) (hf : ∀ g : G, ρ g ≫ f = f)
    {a b : affineSchemeActionQuotient G ρ h₁ hcomp f hf ⟶ T}
    (h : affineSchemeActionQuotientMap G ρ h₁ hcomp f hf ≫ a =
      affineSchemeActionQuotientMap G ρ h₁ hcomp f hf ≫ b) : a = b := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  apply affineInvariantQuotientMap_cancel Γ(S, ⊤) Γ(X, ⊤) G
  apply (cancel_epi X.isoSpec.hom).mp
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

end AllCharacteristics
