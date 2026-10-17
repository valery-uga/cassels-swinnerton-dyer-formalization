import PfaffianDescent.ActualProjectiveLinePolynomialChartDifferentialFrame
import PfaffianDescent.ActualOpenDifferentialSheafDerivationAction

/- SOURCE ONLY / UNVERIFIED. Genuine ORIGINAL P1 chart differential comparison
on EVERY native source test open and EVERY original coordinate/ring section. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native inverse component identity before supplying actual differential objects. -/
private theorem nativeSchemeModuleIso_inv_hom_app
    {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens)
    (s : M.val.obj (op U)) :
    e.inv.val.app (op U) (e.hom.val.app (op U) s) = s := by
  let F := Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)
  exact ConcreteCategory.congr_hom (F.mapIso e).hom_inv_id s

/-- Inverse of the SAME genuine open-immersion differential restriction Iso,
with its action DERIVED from the proved original universal-D forward action. -/
theorem actualOpenImmersionDifferentialSheafIso_inverse_section_D
    {K : Type u} [CommRing K] {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (.of K))
    (V : Y.Opens) (r : Γ(Y, V)) :
    (actualOpenImmersionDifferentialSheafRestrictionIso f g).inv.val.app (op V)
      (actualRelativeDifferentialSection g (f ''ᵁ V) ((f.appIso V).inv r)) =
        actualRelativeDifferentialSection (f ≫ g) V r := by
  have h := actualOpenImmersionDifferentialSheafIso_section_D f g V r
  rw [← h]
  exact nativeSchemeModuleIso_inv_hom_app
    (actualOpenImmersionDifferentialSheafRestrictionIso f g) V _

/-- A proved equality of ORIGINAL base morphisms carries the genuine universal
D section through its literal native EqToIso. No differential equality premise. -/
theorem actualRelativeDifferentials_eqToIso_hom_D
    {K : Type u} [CommRing K] {Y : Scheme.{u}}
    {g g' : Y ⟶ Spec (.of K)} (h : g = g') (V : Y.Opens) (r : Γ(Y, V)) :
    (eqToIso (congrArg (fun f : Y ⟶ Spec (.of K) => schemeRelativeDifferentials f) h)).hom.val.app
        (op V) (actualRelativeDifferentialSection g V r) =
      actualRelativeDifferentialSection g' V r := by
  cases h
  rfl

/-- Combine native inverse D action with a proved base-map equality BEFORE
inserting the original polynomial/P1 module factories. -/
private theorem originalOpenDifferentialInverseD_baseEquality002
    {K : Type u} [CommRing K] {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (.of K))
    (g' : Y ⟶ Spec (.of K)) (h : f ≫ g = g')
    (V : Y.Opens) (r : Γ(Y, V)) :
    (eqToIso (congrArg (fun k => schemeRelativeDifferentials k) h)).hom.val.app (op V)
      ((actualOpenImmersionDifferentialSheafRestrictionIso f g).inv.val.app (op V)
        (actualRelativeDifferentialSection g (f ''ᵁ V) ((f.appIso V).inv r))) =
      actualRelativeDifferentialSection g' V r := by
  have hi := actualOpenImmersionDifferentialSheafIso_inverse_section_D f g V r
  have hc := congrArg
    (fun z : (schemeRelativeDifferentials (f ≫ g)).val.obj (op V) =>
      (eqToIso (congrArg (fun k => schemeRelativeDifferentials k) h)).hom.val.app (op V) z) hi
  exact hc.trans (actualRelativeDifferentials_eqToIso_hom_D h V r)

/-- Actual original P1 chart/open differential-to-affine comparison for EVERY
native chart test open and section. All comparison/base data supplied internally. -/
theorem actualProjectiveLinePolynomialChartDifferential_toAffine_D
    (K : Type u) [CommRing K] (b : Bool)
    (V : (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).Opens)
    (r : Γ(Spec (.of (MvPolynomial {i : Bool // i ≠ b} K)), V)) :
    let f := actualProjectiveLinePolynomialChartToLine K b
    let g := projectiveLineProjToBase K
    let h := actualProjectiveLinePolynomialChartToLine_toBase K b
    (eqToIso (congrArg (fun k => schemeRelativeDifferentials k) h)).hom.val.app (op V)
      ((actualOpenImmersionDifferentialSheafRestrictionIso f g).inv.val.app (op V)
        (actualRelativeDifferentialSection g (f ''ᵁ V) ((f.appIso V).inv r))) =
      actualRelativeDifferentialSection
        (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial {i : Bool // i ≠ b} K)))) V r := by
  exact originalOpenDifferentialInverseD_baseEquality002
    (actualProjectiveLinePolynomialChartToLine K b) (projectiveLineProjToBase K)
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial {i : Bool // i ≠ b} K))))
    (actualProjectiveLinePolynomialChartToLine_toBase K b) V r

end PfaffianDescent
end
