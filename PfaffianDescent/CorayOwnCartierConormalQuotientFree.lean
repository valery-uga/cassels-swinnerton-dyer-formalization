import PfaffianDescent.CorayRegularPrincipalNativeConormal
import PfaffianDescent.CorayQuotientNativeConormalSheaf
import PfaffianDescent.CorayRegularPrincipalNativeConormalChart
import PfaffianDescent.ClosedImmersionIdealBaseChange

/-! SOURCE ONLY / UNVERIFIED. Local native conormal trivializations for the
actual Cartier immersion. The quotient action and actual chart pullbacks are
unchanged. This is a local adjunction input, not a genus or Euler estimate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- The actual regular principal conormal is free over its OWN quotient
ring, with the independently canonical quotient action. Its underlying map
is the existing ambient-linear class-of-equation map. -/
def regularPrincipalConormalQuotientLinearEquiv
    {A : Type u} [CommRing A] (x : A) (hx : IsRegular x) :
    (A ⧸ Ideal.span ({x} : Set A)) ≃ₗ[A ⧸ Ideal.span ({x} : Set A)]
      (Ideal.span ({x} : Set A)).Cotangent := by
  let I := Ideal.span ({x} : Set A)
  let e := regularPrincipalConormalLinearEquiv x hx
  refine { toAddEquiv := e.toAddEquiv, map_smul' := ?_ }
  intro b t
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  change e ((algebraMap A (A ⧸ I) a) • t) =
    (algebraMap A (A ⧸ I) a) • e t
  simpa only [algebraMap_smul] using e.map_smul a t

/-- Actual conormal of the canonical affine quotient by a regular equation,
identified with its OWN structure sheaf by the native quotient-linear map. -/
def regularPrincipalAffineQuotientConormalUnitIso
    {A : Type u} [CommRing A] (x : A) (hx : IsRegular x) :
    actualClosedImmersionConormalModule
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span ({x} : Set A))))) ≅
      SheafOfModules.unit
        (Spec (CommRingCat.of (A ⧸ Ideal.span ({x} : Set A)))).ringCatSheaf := by
  let I := Ideal.span ({x} : Set A)
  let e := regularPrincipalConormalQuotientLinearEquiv x hx
  exact affineQuotientNativeConormalTildeIso I ≪≫
    (tilde.functor (CommRingCat.of (A ⧸ I))).mapIso e.symm.toModuleIso ≪≫
    AlgebraicGeometry.tildeSelf

/-- Unit trivialization of the SAME global conormal on the SAME actual
regular-principal source chart. The actual quotientKer presentation and
pullback-unit comparison derive the Iso; no conormal rank or Iso is input. -/
def RegularPrincipalImmersion.actualChartConormalUnitIso
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (a : H.Index) :
    (Scheme.Modules.pullback (H.source a)).obj
        (actualClosedImmersionConormalModule i) ≅
      SheafOfModules.unit (Spec (H.B a)).ringCatSheaf := by
  let rho := (H.ringMap a).hom
  let I := RingHom.ker rho
  let eRing := rho.quotientKerEquivOfSurjective (H.ringMap_surjective a)
  let j := Spec.map (CommRingCat.ofHom eRing.toRingHom)
  have hfree : Nonempty
      ((H.A a ⧸ I) ≃ₗ[H.A a ⧸ I] I.Cotangent) := by
    obtain ⟨x, hx, hkernel⟩ := H.principal a
    let P : Ideal (H.A a) → Prop := fun J =>
      Nonempty ((H.A a ⧸ J) ≃ₗ[H.A a ⧸ J] J.Cotangent)
    have hI : I = Ideal.span ({x} : Set (H.A a)) := hkernel
    have hspan : P (Ideal.span ({x} : Set (H.A a))) :=
      ⟨regularPrincipalConormalQuotientLinearEquiv x hx⟩
    change P I
    exact Eq.mpr (congrArg P hI) hspan
  let eC := Classical.choice hfree
  let eT : (tilde.functor (CommRingCat.of (H.A a ⧸ I))).obj
        (ModuleCat.of (H.A a ⧸ I) I.Cotangent) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (H.A a ⧸ I))).ringCatSheaf :=
    (tilde.functor (CommRingCat.of (H.A a ⧸ I))).mapIso eC.symm.toModuleIso ≪≫
      AlgebraicGeometry.tildeSelf
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison j) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison j
  exact H.actualChartNativeConormalQuotientTildeIso a ≪≫
    (Scheme.Modules.pullback j).mapIso eT ≪≫
    asIso (BundleSectionZeroLocus.pullbackUnitComparison j)

end PfaffianDescent
end
