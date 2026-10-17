import PfaffianDescent.VoisinDegreeElevenSerreIncidenceBundleCoordinates
import PfaffianDescent.AffineFreeModuleBaseChange

/-! # Literal native Gamma coordinates of an actual free point fibre -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceSpecFibreCoordinateEquiv
    (E : Type u) [Field E] (I : Type u) [Fintype I] [DecidableEq I]
    (M : (Spec (.of E)).Modules)
    (t : SheafOfModules.free (R := (Spec (.of E)).ringCatSheaf) I ≅ M) :
    (moduleSpecΓFunctor (R := CommRingCat.of E)).obj M ≃ₗ[E] (I → E) := by
  let q := moduleOpenTopLinearEquivOfFreeIso I M t
  exact {
    toFun := fun s i => (Scheme.ΓSpecIso (.of E)).hom (q s i)
    invFun := fun v => q.symm (fun i => (Scheme.ΓSpecIso (.of E)).inv (v i))
    left_inv := by
      intro s
      change q.symm (fun i => (Scheme.ΓSpecIso (.of E)).inv
        ((Scheme.ΓSpecIso (.of E)).hom (q s i))) = s
      have hv : (fun i => (Scheme.ΓSpecIso (.of E)).inv
          ((Scheme.ΓSpecIso (.of E)).hom (q s i))) = q s := by
        funext i
        exact Iso.hom_inv_id_apply _ _
      rw [hv, q.symm_apply_apply]
    right_inv := by
      intro v
      funext i
      change (Scheme.ΓSpecIso (.of E)).hom
        (q (q.symm (fun i => (Scheme.ΓSpecIso (.of E)).inv (v i))) i) = v i
      rw [q.apply_symm_apply]
      exact Iso.inv_hom_id_apply _ _
    map_add' := by
      intro s v
      funext i
      exact (congrArg (fun w => (Scheme.ΓSpecIso (.of E)).hom (w i))
        (q.map_add s v)).trans (map_add _ _ _)
    map_smul' := by
      intro a s
      funext i
      exact (congrArg (fun w => (Scheme.ΓSpecIso (.of E)).hom (w i))
        (q.map_smul ((Scheme.ΓSpecIso (.of E)).inv a) (show Γ(M, ⊤) from s))).trans
          (by
            change (Scheme.ΓSpecIso (.of E)).hom
              ((Scheme.ΓSpecIso (.of E)).inv a * q s i) = _
            rw [map_mul, Iso.inv_hom_id_apply]) }

theorem serreIncidenceSpecFibreCoordinateEquiv_section
    (E : Type u) [Field E] (I : Type u) [Fintype I] [DecidableEq I]
    (M : (Spec (.of E)).Modules)
    (t : SheafOfModules.free (R := (Spec (.of E)).ringCatSheaf) I ≅ M)
    (s : M.sections) (i : I) :
    serreIncidenceSpecFibreCoordinateEquiv E I M t (s.val (op ⊤)) i =
      (Scheme.ΓSpecIso (.of E)).hom
        (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I t s i) := by
  change (Scheme.ΓSpecIso (.of E)).hom
    (moduleOpenTopLinearEquivOfFreeIso I M t (s.val (op ⊤)) i) = _
  rw [moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate]
  change (Scheme.ΓSpecIso (.of E)).hom (BundleSectionZeroLocus.freeSectionCoordinate I
    (SheafOfModules.sectionsMap t.inv ((schemeModuleSectionsEquivTop M).symm
      ((schemeModuleSectionsEquivTop M) s))) i) = _
  rw [Equiv.symm_apply_apply]
  rfl

end PfaffianDescent
