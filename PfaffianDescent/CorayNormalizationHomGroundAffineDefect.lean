import PfaffianDescent.SchemeModuleUnitHomGroundSections
import PfaffianDescent.CorayGlobalSectionsChosenAffineDefect

/-! Actual unit Hom of the SAME canonical normalization quotient identifies
with literal global sections and the EXISTING actual chosen affine defect.
No finite-dimensionality, constants equality, genus or reduction conclusion.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K]

/-- Actual Hom(O_X,Q) for the canonical GLOBAL Q equals literal Γ(Q,top)
over the original K. It requires no support, affine, QC or Ext hypothesis. -/
def genericNormalizationUnitHomGroundLinearEquivOpenTop
    (X : Scheme.{u}) [IsIntegral X] (pi : X ⟶ Spec (CommRingCat.of K)) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      genericNormalizationQuotientSheaf X) ≃ₗ[K]
      SchemeModuleOpenSectionsOver pi (genericNormalizationQuotientSheaf X) ⊤ := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact schemeModuleUnitHomGroundLinearEquivOpenTop pi (genericNormalizationQuotientSheaf X)

/-- The comparison preserves the literal original global cokernel projection
as a map on actual sections; it is not replaced by an arbitrary quotient map. -/
theorem genericNormalizationUnitHomGroundLinearEquivOpenTop_projection
    (X : Scheme.{u}) [IsIntegral X] (pi : X ⟶ Spec (CommRingCat.of K)) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let P := (Scheme.Modules.pushforward ν).obj (SheafOfModules.unit N.ringCatSheaf)
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ∀ s : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ P,
      genericNormalizationUnitHomGroundLinearEquivOpenTop X pi
          (s ≫ cokernel.π (genericNormalizationUnitToPushforwardUnit X)) =
        (cokernel.π (genericNormalizationUnitToPushforwardUnit X)).val.app (op ⊤)
          (schemeModuleUnitHomGroundLinearEquivOpenTop pi P s) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact fun s ↦ schemeModuleUnitHomGroundLinearEquivOpenTop_naturality pi
    (cokernel.π (genericNormalizationUnitToPushforwardUnit X)) s

/-- The actual Hom-category K-action is preserved by restriction to an
actual nonempty affine open containing every actual closed Q-support point,
then by the EXISTING literal normalization-defect comparison on that open.
All section/comparison/scalar compatibility is derived by the actual sources. -/
def genericNormalizationUnitHomGroundLinearEquivAffineDefect
    (X : Scheme.{u}) [IsIntegral X] (pi : X ⟶ Spec (CommRingCat.of K))
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let beta : K →+* Γ(X, U) :=
      (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      genericNormalizationQuotientSheaf X) ≃ₗ[K]
      (ModuleCat.restrictScalars beta).obj
        (ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField)) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let Q := genericNormalizationQuotientSheaf X
  let beta : K →+* Γ(X, U) :=
    (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let D := (ModuleCat.restrictScalars beta).obj
    (ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField))
  let eGlobal : SchemeModuleGlobalSectionsOver pi Q ≃ₗ[K]
      SchemeModuleOpenSectionsOver pi Q U :=
    schemeModule_groundGlobalSectionsEquiv_of_closedSupport_subset pi Q U
      (schemeModuleStalkSupport Q) hclosed (Set.Subset.rfl) hsU
  let eAffine : SchemeModuleOpenSectionsOver pi Q U ≃ₗ[K] D :=
    (genericNormalizationQuotientSheaf_groundAffineSectionsIso K X pi U hU).toLinearEquiv
  exact (schemeModuleUnitHomGroundLinearEquivGlobalSections pi Q).trans
    (eGlobal.trans eAffine)

/-- The actual affine comparison has the explicit original restriction and
original affine quotient comparison as its value map. In particular the
canonical global projection can be substituted using the preceding square. -/
theorem genericNormalizationUnitHomGroundLinearEquivAffineDefect_apply
    (X : Scheme.{u}) [IsIntegral X] (pi : X ⟶ Spec (CommRingCat.of K))
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ∀ s : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
        genericNormalizationQuotientSheaf X,
      genericNormalizationUnitHomGroundLinearEquivAffineDefect X pi hclosed U hU hsU s =
        (genericNormalizationQuotientSheaf_groundAffineSectionsIso K X pi U hU).hom
          ((genericNormalizationQuotientSheaf X).presheaf.map
            (homOfLE (show U ≤ ⊤ from le_top)).op
              (s.val.app (op ⊤) (1 : Γ(X, ⊤)))) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact fun _ ↦ rfl

/-- Literal original CharZero smooth-cubic/selected-curve data derive the
actual support and affine choice internally through the existing global
defect construction. The resulting Hom equivalence retains original K and Q.
No finite-dimensionality, constants, genus or comparison certificate input. -/
theorem projectiveIntersection_genericNormalizationQuotient_exists_unitHomGroundLinearEquiv_affineDefect
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (x : scheme (projectiveIntersectionIdeal p q hp hq)) :
    ∃ (U : (scheme (projectiveIntersectionIdeal p q hp hq)).affineOpens)
      (hU : Nonempty U.1),
      letI : Nonempty U.1 := hU
      let X := scheme (projectiveIntersectionIdeal p q hp hq)
      let pi := toBase (projectiveIntersectionIdeal p q hp hq)
      letI : Linear K X.Modules := schemeModulesLinearOver pi
      x ∈ U.1 ∧ Nonempty
        (((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
          genericNormalizationQuotientSheaf X) ≃ₗ[K]
          (ModuleCat.restrictScalars
            ((pi.appLE ⊤ U.1 (by simp)).hom.comp
              (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).obj
            (ModuleCat.of Γ(X, U.1)
              (localNormalizationDefect Γ(X, U.1) X.functionField))) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  let Q := genericNormalizationQuotientSheaf X
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  obtain ⟨U, hnonempty, hxU, ⟨E⟩⟩ :=
    projectiveIntersection_genericNormalizationQuotient_exists_globalSectionsEquiv_affineDefect
      p q hp hp0 n hq hnot x
  letI : Nonempty U.1 := hnonempty
  exact ⟨U, hnonempty, hxU,
    ⟨(schemeModuleUnitHomGroundLinearEquivGlobalSections pi Q).trans E⟩⟩

end PfaffianDescent.Coray
