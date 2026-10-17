import PfaffianDescent.CorayWholePlaneIdealNativeSectionKernel
import PfaffianDescent.CorayWholeIdealGradeRestriction
import PfaffianDescent.ActualP3IdealGlobalRestrictionKernel

/-! The genuine whole quotient-ideal grade embeds into the SAME native
ideal-twist H0. This map factors the actual homogeneous global section map
through the literal ideal-twist sequence. No H0 surjectivity is claimed.
SOURCE ONLY: compiler acceptance remains pending. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native kernel equivalence preserves the SAME first map. -/
lemma shortExactActualGlobalSectionsKernelEquiv_val
    {X : Scheme.{u}} (pi : X ⟶ Spec (.of K))
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (s : SchemeModuleGlobalSectionsOver pi S.X₁) :
    (shortExactActualGlobalSectionsKernelEquiv pi S hS s).val =
      schemeModuleGlobalSectionsMap pi S.f s := rfl

/-- The inverse kernel equivalence preserves the literal first map. -/
lemma shortExactActualGlobalSectionsKernelEquiv_symm_val
    {X : Scheme.{u}} (pi : X ⟶ Spec (.of K))
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (s : (schemeModuleGlobalSectionsMap pi S.g).ker) :
    (shortExactActualGlobalSectionsKernelEquiv pi S hS).symm s ≫ S.f = s.val := by
  have h := congrArg Subtype.val
    ((shortExactActualGlobalSectionsKernelEquiv pi S hS).apply_symm_apply s)
  rw [shortExactActualGlobalSectionsKernelEquiv_val] at h
  change (shortExactActualGlobalSectionsKernelEquiv pi S hS).symm s ≫ S.f = s.val at h
  exact h

/-- The SAME homogeneous ambient section has a canonical native ideal
section lift, defined using the actual sequence's kernel universal property. -/
def wholePlaneIdealGradeNativeGlobalSectionLinearMap
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) :
    letI : IsClosedImmersion (schemeQuotientMap I J hIJ) :=
      schemeQuotientMap_closedImmersion I J hIJ
    wholeIdealGrade (grading I)
      (J.toIdeal.map (Ideal.Quotient.mk I.toIdeal)) d →ₗ[K]
      SchemeModuleGlobalSectionsOver (toBase I)
        (closedImmersionIdealTwist (schemeQuotientMap I J hIJ)
          (positiveSheafOfModules (grading I) d)) := by
  let i := schemeQuotientMap I J hIJ
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion I J hIJ
  let T := positiveSheafOfModules (grading I) d
  let S := closedImmersionIdealTwistSequence i T
  let e := schemeModuleTensorUnitLeftIso T
  let hS : S.ShortExact := quotientPositiveTwist_closedImmersionIdealTwistSequence_shortExact I i d
  let v : wholeIdealGrade (grading I)
      (J.toIdeal.map (Ideal.Quotient.mk I.toIdeal)) d →ₗ[K] grading I d :=
    { toFun a := ⟨a.val, a.property.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let a := (schemeModuleGlobalSectionsMap (toBase I) e.inv).comp
    ((positiveHomogeneousGlobalSectionLinearMap I d).comp v)
  let r := schemeModuleGlobalSectionsMap (toBase I) S.g
  have hker : ∀ x, a x ∈ r.ker := by
    intro x
    apply LinearMap.mem_ker.mpr
    change (positiveHomogeneousGlobalSectionLinearMap I d
      ⟨x.val, x.property.2⟩ ≫ e.inv) ≫ S.g = 0
    simpa only [Category.assoc] using
      wholePlaneQuotientIdeal_homogeneousSection_nativeRestriction_zero
        I J hIJ d ⟨x.val, x.property.2⟩ x.property.1
  exact (shortExactActualGlobalSectionsKernelEquiv (toBase I) S hS).symm.toLinearMap.comp
    (a.codRestrict r.ker hker)

/-- The canonical lift followed by the ACTUAL ideal augmentation is
literally the original homogeneous global section, not just a rank equality. -/
theorem wholePlaneIdealGradeNativeGlobalSectionLinearMap_inclusion
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ)
    (x : wholeIdealGrade (grading I)
      (J.toIdeal.map (Ideal.Quotient.mk I.toIdeal)) d) :
    letI : IsClosedImmersion (schemeQuotientMap I J hIJ) :=
      schemeQuotientMap_closedImmersion I J hIJ
    wholePlaneIdealGradeNativeGlobalSectionLinearMap I J hIJ d x ≫
      (closedImmersionIdealTwistSequence (schemeQuotientMap I J hIJ)
        (positiveSheafOfModules (grading I) d)).f ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules (grading I) d)).hom =
      positiveHomogeneousGlobalSectionLinearMap I d ⟨x.val, x.property.2⟩ := by
  let i := schemeQuotientMap I J hIJ
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion I J hIJ
  let T := positiveSheafOfModules (grading I) d
  let S := closedImmersionIdealTwistSequence i T
  let e := schemeModuleTensorUnitLeftIso T
  let hS : S.ShortExact := quotientPositiveTwist_closedImmersionIdealTwistSequence_shortExact I i d
  let E := shortExactActualGlobalSectionsKernelEquiv (toBase I) S hS
  have hlift : wholePlaneIdealGradeNativeGlobalSectionLinearMap I J hIJ d x ≫ S.f =
      positiveHomogeneousGlobalSectionLinearMap I d ⟨x.val, x.property.2⟩ ≫ e.inv := by
    change E.symm _ ≫ S.f = _
    exact shortExactActualGlobalSectionsKernelEquiv_symm_val (toBase I) S hS _
  change _ ≫ S.f ≫ e.hom = _
  rw [← Category.assoc, hlift]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- On a nonempty integral projective quotient, the genuine whole ideal
coordinate grade embeds into its actual native ideal-twist H0. -/
theorem wholePlaneIdealGradeNativeGlobalSectionLinearMap_injective
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) [IsDomain (CoordinateRing I)] [Nonempty (scheme I)]
    (d : ℕ) :
    letI : IsClosedImmersion (schemeQuotientMap I J hIJ) :=
      schemeQuotientMap_closedImmersion I J hIJ
    Function.Injective (wholePlaneIdealGradeNativeGlobalSectionLinearMap I J hIJ d) := by
  letI : IsClosedImmersion (schemeQuotientMap I J hIJ) :=
    schemeQuotientMap_closedImmersion I J hIJ
  intro x y hxy
  have h := congrArg (fun t => t ≫
      (closedImmersionIdealTwistSequence (schemeQuotientMap I J hIJ)
        (positiveSheafOfModules (grading I) d)).f ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules (grading I) d)).hom) hxy
  rw [wholePlaneIdealGradeNativeGlobalSectionLinearMap_inclusion,
    wholePlaneIdealGradeNativeGlobalSectionLinearMap_inclusion] at h
  have heq := positiveHomogeneousGlobalSectionLinearMap_injective I d h
  exact Subtype.ext (congrArg (fun z : grading I d => (z : CoordinateRing I)) heq)

/-- The same lift in the native top-open H0 model, with pi-induced scalars. -/
def wholePlaneIdealGradeNativeTopSectionLinearMap
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) :
    letI : IsClosedImmersion (schemeQuotientMap I J hIJ) :=
      schemeQuotientMap_closedImmersion I J hIJ
    wholeIdealGrade (grading I)
      (J.toIdeal.map (Ideal.Quotient.mk I.toIdeal)) d →ₗ[K]
      SchemeModuleOpenSectionsOver (toBase I)
        (closedImmersionIdealTwist (schemeQuotientMap I J hIJ)
          (positiveSheafOfModules (grading I) d)) ⊤ := by
  letI : IsClosedImmersion (schemeQuotientMap I J hIJ) :=
    schemeQuotientMap_closedImmersion I J hIJ
  exact (schemeModuleGlobalSectionsLinearEquivOpenTop (toBase I)
    (closedImmersionIdealTwist (schemeQuotientMap I J hIJ)
      (positiveSheafOfModules (grading I) d))).toLinearMap.comp
        (wholePlaneIdealGradeNativeGlobalSectionLinearMap I J hIJ d)

/-- Native H0 injection retains the SAME coefficient and base map. -/
theorem wholePlaneIdealGradeNativeTopSectionLinearMap_injective
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) [IsDomain (CoordinateRing I)] [Nonempty (scheme I)]
    (d : ℕ) :
    letI : IsClosedImmersion (schemeQuotientMap I J hIJ) :=
      schemeQuotientMap_closedImmersion I J hIJ
    Function.Injective (wholePlaneIdealGradeNativeTopSectionLinearMap I J hIJ d) := by
  letI : IsClosedImmersion (schemeQuotientMap I J hIJ) :=
    schemeQuotientMap_closedImmersion I J hIJ
  exact (schemeModuleGlobalSectionsLinearEquivOpenTop (toBase I)
      (closedImmersionIdealTwist (schemeQuotientMap I J hIJ)
        (positiveSheafOfModules (grading I) d))).injective.comp
    (wholePlaneIdealGradeNativeGlobalSectionLinearMap_injective I J hIJ d)

end PfaffianDescent.Coray
end
