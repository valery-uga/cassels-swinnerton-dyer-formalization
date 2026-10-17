import PfaffianDescent.CorayGenericNormalizationAffineDefectLinearExact
import PfaffianDescent.CorayGlobalAffineCokernelProjection

/-! The SAME global canonical normalization projection gives the literal
integral-closure quotient class on the chosen actual affine open.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Evaluate an ordinary ModuleCat square before actual normalization,
section, integral-closure and restriction-of-scalars objects are substituted. -/
private theorem moduleCatSquarePointwise002
    {R : Type u} [CommRing R] {M N Q S : ModuleCat.{u} R}
    {a : M ⟶ N} {b : N ⟶ Q} {d : M ⟶ S} {c : S ⟶ Q}
    (h : a ≫ b = d ≫ c) : ∀ x : M, b (a x) = c (d x) := by
  intro x
  exact ConcreteCategory.congr_hom h x

/-- Capture the already proved ORIGINAL module-morphism square as a
pointwise law separately from the public quotient-class header. No map changes. -/
private def originalNormalizationProjectionPointwise002
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :=
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
    ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
  moduleCatSquarePointwise002
    (genericNormalizationQuotientSheaf_affineSectionsIso_π X U hU)

/-- The actual GLOBAL sheaf projection, evaluated on this affine open,
becomes the literal quotient class after the EXISTING actual comparison. -/
theorem genericNormalizationQuotientSheaf_affineSectionsIso_π_apply
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
      ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
    ∀ x : Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U),
      (genericNormalizationQuotientSheaf_affineSectionsIso X U hU).hom
        ((cokernel.π (genericNormalizationUnitToPushforwardUnit X)).val.app (op U) x) =
      (LinearMap.range (Algebra.linearMap Γ(X, U)
        (integralClosure Γ(X, U) X.functionField))).mkQ
          (genericNormalization_preimageSectionsAlgEquiv X U hU x) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
    ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
  change ∀ x : Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U),
      (genericNormalizationQuotientSheaf_affineSectionsIso X U hU).hom
        ((cokernel.π (genericNormalizationUnitToPushforwardUnit X)).val.app (op U) x) =
      (LinearMap.range (Algebra.linearMap Γ(X, U)
        (integralClosure Γ(X, U) X.functionField))).mkQ
          (genericNormalization_preimageSectionsAlgEquiv X U hU x)
  exact originalNormalizationProjectionPointwise002 X U hU

/-- The same literal quotient-class formula retains the original K-action
through the EXISTING pi-induced restriction of scalars; no action is changed. -/
theorem genericNormalizationQuotientSheaf_groundAffineSectionsIso_π_apply
    (K : Type u) [CommRing K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
      ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
    ∀ x : Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U),
      (genericNormalizationQuotientSheaf_groundAffineSectionsIso K X pi U hU).hom
        ((cokernel.π (genericNormalizationUnitToPushforwardUnit X)).val.app (op U) x) =
      (LinearMap.range (Algebra.linearMap Γ(X, U)
        (integralClosure Γ(X, U) X.functionField))).mkQ
          (genericNormalization_preimageSectionsAlgEquiv X U hU x) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
    ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
  change ∀ x : Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U),
      (genericNormalizationQuotientSheaf_groundAffineSectionsIso K X pi U hU).hom
        ((cokernel.π (genericNormalizationUnitToPushforwardUnit X)).val.app (op U) x) =
      (LinearMap.range (Algebra.linearMap Γ(X, U)
        (integralClosure Γ(X, U) X.functionField))).mkQ
          (genericNormalization_preimageSectionsAlgEquiv X U hU x)
  exact genericNormalizationQuotientSheaf_affineSectionsIso_π_apply X U hU

/-- The EXISTING K-linear global contribution σ is exactly the class of the
actual restricted normalization function. Its image is retained, not erased. -/
theorem genericNormalizationAffineDefectProjectionLinearMap_quotientClass_apply
    {K : Type u} [Field K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let P := (Scheme.Modules.pushforward ν).obj (SheafOfModules.unit N.ringCatSheaf)
    letI : Algebra Γ(X, U) Γ(N, ν ⁻¹ᵁ U) := (ν.app U).hom.toAlgebra
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ∀ s : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ P,
      genericNormalizationAffineDefectProjectionLinearMap X pi hclosed U hU hsU s =
        (LinearMap.range (Algebra.linearMap Γ(X, U)
          (integralClosure Γ(X, U) X.functionField))).mkQ
            (genericNormalization_preimageSectionsAlgEquiv X U hU
              (P.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
                (s.val.app (op ⊤) (1 : Γ(X, ⊤))))) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let P := (Scheme.Modules.pushforward ν).obj (SheafOfModules.unit N.ringCatSheaf)
  letI : Algebra Γ(X, U) Γ(N, ν ⁻¹ᵁ U) := (ν.app U).hom.toAlgebra
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let Q := genericNormalizationQuotientSheaf X
  let πq := cokernel.π (genericNormalizationUnitToPushforwardUnit X)
  let i := (homOfLE (show U ≤ ⊤ from le_top)).op
  change ∀ s : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ P,
      genericNormalizationAffineDefectProjectionLinearMap X pi hclosed U hU hsU s =
        (LinearMap.range (Algebra.linearMap Γ(X, U)
          (integralClosure Γ(X, U) X.functionField))).mkQ
            (genericNormalization_preimageSectionsAlgEquiv X U hU
              (P.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
                (s.val.app (op ⊤) (1 : Γ(X, ⊤)))))
  intro s
  let z := s.val.app (op ⊤) (1 : Γ(X, ⊤))
  have hn : Q.presheaf.map i ((s ≫ πq).val.app (op ⊤) (1 : Γ(X, ⊤))) =
      πq.val.app (op U) (P.presheaf.map i z) := by
    exact (ConcreteCategory.congr_hom (πq.val.naturality i) z).symm
  calc
    _ = genericNormalizationUnitHomGroundLinearEquivAffineDefect X pi hclosed U hU hsU
        (s ≫ πq) := genericNormalizationAffineDefectProjectionLinearMap_apply X pi hclosed U hU hsU s
    _ = (genericNormalizationQuotientSheaf_groundAffineSectionsIso K X pi U hU).hom
        (Q.presheaf.map i ((s ≫ πq).val.app (op ⊤) (1 : Γ(X, ⊤)))) :=
      genericNormalizationUnitHomGroundLinearEquivAffineDefect_apply X pi hclosed U hU hsU (s ≫ πq)
    _ = (genericNormalizationQuotientSheaf_groundAffineSectionsIso K X pi U hU).hom
        (πq.val.app (op U) (P.presheaf.map i z)) := congrArg (fun t ↦
          (genericNormalizationQuotientSheaf_groundAffineSectionsIso K X pi U hU).hom t) hn
    _ = _ := genericNormalizationQuotientSheaf_groundAffineSectionsIso_π_apply K X pi U hU
      (P.presheaf.map i z)

end PfaffianDescent.Coray
