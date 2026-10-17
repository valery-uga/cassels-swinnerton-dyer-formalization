import PfaffianDescent.CorayPushforwardCechGroundLinearity
import PfaffianDescent.SchemeModuleOpenTopConnectingLinearExact
import AllCharacteristics.ClosedPointAlgebra

/-! Original-K sections of the ACTUAL point fiber. Its source action is
induced by the actual base morphism; the residue action is the existing
pointAlgebra of the same point-to-base map. A chosen actual fiber frame
gives an equivalence; its dimension is the full actual residue degree.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {K : Type u} [Field K]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The existing genuine pushforward section comparison on the top open.
Both original actions are independent, induced by pi and f >> pi. -/
def schemeModulePushforward_topSectionsLinearEquiv
    {X Y : Scheme.{u}} (pi : X ⟶ Spec (CommRingCat.of K))
    (f : Y ⟶ X) (M : Y.Modules) :
    SchemeModuleOpenSectionsOver pi ((Scheme.Modules.pushforward f).obj M) ⊤ ≃ₗ[K]
      SchemeModuleOpenSectionsOver (f ≫ pi) M ⊤ := by
  simpa only [Scheme.Hom.preimage_top] using
    schemeModulePushforward_openSectionsLinearEquiv pi f M ⊤

/-- Actual field-spectrum functions, with the independently pi-induced
section action, equal the field with the actual Spec-preimage algebra.
Scalar compatibility is proved, not defined through this equivalence. -/
def schemeModuleFieldSpecUnitTopLinearEquiv
    {L : Type u} [Field L] (rho : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) :
    letI : Algebra K L := (Spec.preimage rho).hom.toAlgebra
    SchemeModuleOpenSectionsOver rho
      (SheafOfModules.unit (Spec (CommRingCat.of L)).ringCatSheaf) ⊤ ≃ₗ[K] L := by
  let beta := (Spec.preimage rho).hom
  letI : Algebra K L := beta.toAlgebra
  let e := (Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv
  have hc (c : K) : e (affineFunctionHom rho c) = beta c := by
    have h := Scheme.ΓSpecIso_inv_naturality (Spec.preimage rho)
    rw [Spec.map_preimage rho] at h
    have hvalue := ConcreteCategory.congr_hom h c
    change e.symm (beta c) = affineFunctionHom rho c at hvalue
    rw [← hvalue, e.apply_symm_apply]
  refine { toAddEquiv := e.toAddEquiv, map_smul' := ?_ }
  intro c s
  change e (schemeOpenBaseRingHom rho ⊤ c *
    (show (Spec (CommRingCat.of L)).presheaf.obj (op ⊤) from s)) = beta c * e s
  rw [schemeOpenBaseRingHom_top_apply, e.map_mul, hc]

/-- A CHOSEN actual frame of i^*T yields an actual original-K equivalence
from SAME i_*i^*T sections to κ(P), using SAME pointAlgebra. Neither the
intrinsic fiber nor its original scalar is replaced to obtain linearity. -/
def schemeModuleResiduePointFiberTopGroundLinearEquiv
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X) (T : X.Modules)
    (e : (Scheme.Modules.pullback (X.fromSpecResidueField P.1)).obj T ≅
      SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf) :
    letI := AllCharacteristics.pointAlgebra pi P.1
    SchemeModuleOpenSectionsOver pi
      ((Scheme.Modules.pushforward (X.fromSpecResidueField P.1)).obj
        ((Scheme.Modules.pullback (X.fromSpecResidueField P.1)).obj T)) ⊤ ≃ₗ[K]
      X.residueField P.1 := by
  letI := AllCharacteristics.pointAlgebra pi P.1
  let i := X.fromSpecResidueField P.1
  exact (schemeModuleOpenTopIsoLinearEquivOver pi
    ((Scheme.Modules.pushforward i).mapIso e)).trans
      ((schemeModulePushforward_topSectionsLinearEquiv pi i
        (SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)).trans
        (schemeModuleFieldSpecUnitTopLinearEquiv (i ≫ pi)))

/-- A framed actual fiber is finite over original K and has the FULL
scheme residue degree. Generic frame input is internally discharged by
the primitive point-ideal caller; there is no dimension certificate. -/
theorem schemeModuleResiduePointFiberTop_finite_and_finrank
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (P : closedPoints X) (T : X.Modules)
    (e : (Scheme.Modules.pullback (X.fromSpecResidueField P.1)).obj T ≅
      SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf) :
    Module.Finite K (SchemeModuleOpenSectionsOver pi
      ((Scheme.Modules.pushforward (X.fromSpecResidueField P.1)).obj
        ((Scheme.Modules.pullback (X.fromSpecResidueField P.1)).obj T)) ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi
        ((Scheme.Modules.pushforward (X.fromSpecResidueField P.1)).obj
          ((Scheme.Modules.pullback (X.fromSpecResidueField P.1)).obj T)) ⊤) =
        pi.residueDegree P.1 := by
  letI := AllCharacteristics.pointAlgebra pi P.1
  letI : Module.Finite K (X.residueField P.1) := AllCharacteristics.closedPoint_moduleFinite pi P
  let E := schemeModuleResiduePointFiberTopGroundLinearEquiv pi P T e
  exact ⟨Module.Finite.equiv E.symm,
    E.finrank_eq.trans (AllCharacteristics.closedPoint_finrank_eq_residueDegree pi P)⟩

end PfaffianDescent.Coray
