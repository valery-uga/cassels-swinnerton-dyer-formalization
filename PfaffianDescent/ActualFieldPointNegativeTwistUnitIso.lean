import PfaffianDescent.ActualFieldPointPositiveTwistUnitIso
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal
import PfaffianDescent.AffineQuotientPushforwardTilde

/-! SOURCE ONLY / UNVERIFIED. The actual native negative twist at a field
point is trivialized by a genuine coordinate open, with no supplied Iso. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def actualFieldUnitFiberEquiv (L : Type u) [Field L] :
    (moduleSpecΓFunctor (R := .of L)).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) ≃ₗ[L] L :=
  affineGlobalSectionsUnitLinearEquiv (A := L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def actualFieldPointNegativeTwistUnitIso
    {K L : Type u} [Field K] [Field L]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (q : Spec (.of L) ⟶ scheme I) (m : ℕ) :
    (Scheme.Modules.pullback q).obj (sheafOfModules (grading I) m) ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf := by
  let x₀ : Spec (.of L) := (⊥ : PrimeSpectrum L)
  have hx : q x₀ ∈ ⨆ j : Fin 4, quotientCoordinateOpen I j := by
    rw [quotientCoordinateOpen_iSup]
    trivial
  have hchart : ∃ j : Fin 4, q x₀ ∈ quotientCoordinateOpen I j :=
    TopologicalSpace.Opens.mem_iSup.mp hx
  let j : Fin 4 := Classical.choose hchart
  have hj : q x₀ ∈ quotientCoordinateOpen I j := Classical.choose_spec hchart
  let U := quotientCoordinateOpen I j
  have hrange : Set.range q ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    have hx' : q x ∈ U := by
      have he : x = x₀ := Subsingleton.elim _ _
      simpa only [he] using hj
    exact ⟨⟨q x, hx'⟩, rfl⟩
  let qU := IsOpenImmersion.lift U.ι q hrange
  have hfac : qU ≫ U.ι = q := IsOpenImmersion.lift_fac _ _ _
  let T := sheafOfModules (grading I) m
  let eQ := ((Scheme.Modules.pullbackCongr hfac).app T).symm
  let eComp := (Scheme.Modules.pullbackComp qU U.ι).symm.app T
  let eRestr := (Scheme.Modules.pullback qU).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app T)
  let eNeg := (Scheme.Modules.pullback qU).mapIso
    (quotientCoordinateNegativeTwistUnitIso_all I j m)
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison qU) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison qU
  exact eQ ≪≫ eComp ≪≫ eRestr ≪≫ eNeg ≪≫
    asIso (BundleSectionZeroLocus.pullbackUnitComparison qU)

abbrev ActualFieldPointNegativeTwistFiber
    {K L : Type u} [Field K] [Field L]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (q : Spec (.of L) ⟶ scheme I) (m : ℕ) :=
  (moduleSpecΓFunctor (R := .of L)).obj
    ((Scheme.Modules.pullback q).obj (sheafOfModules (grading I) m))

def actualFieldPointNegativeTwistFiberEquiv
    {K L : Type u} [Field K] [Field L]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (q : Spec (.of L) ⟶ scheme I) (m : ℕ) :
    ActualFieldPointNegativeTwistFiber I q m ≃ₗ[L] L :=
  ((moduleSpecΓFunctor (R := .of L)).mapIso
    (actualFieldPointNegativeTwistUnitIso I q m)).toLinearEquiv ≪≫ₗ
      actualFieldUnitFiberEquiv L

lemma actualFieldPointNegativeTwistFiberEquiv_apply
    {K L : Type u} [Field K] [Field L]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (q : Spec (.of L) ⟶ scheme I) (m : ℕ)
    (t : ActualFieldPointNegativeTwistFiber I q m) :
    actualFieldPointNegativeTwistFiberEquiv I q m t =
      (Scheme.ΓSpecIso (.of L)).hom
        ((actualFieldPointNegativeTwistUnitIso I q m).hom.val.app (.op ⊤) t) := rfl

end PfaffianDescent
