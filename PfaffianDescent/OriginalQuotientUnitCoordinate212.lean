import PfaffianDescent.WholeQuotientPointCoefficient202
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! The original quotient-ring unit coordinate used by202 is independent
of its point parameter and middle frame. All ring actions remain explicit. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors
universe u
set_option backward.isDefEq.respectTransparency false

/-- Native original B unit restricted through phi, then the actual original
quotient equivalence inverse. This is the literal coordinate used by202. -/
def originalQuotientUnitCoordinate212
    {R B : Type u} [CommRing R] [CommRing B] (f : R)
    (e : (R ⧸ Ideal.span {f}) ≃+* B)
    (phi : R →+* B) (hphi : phi = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {f}))) :
    (ModuleCat.restrictScalars phi).obj (ModuleCat.of B B) ⟶
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
        (ModuleCat.of (R ⧸ Ideal.span {f}) (R ⧸ Ideal.span {f})) :=
  (ModuleCat.restrictScalarsComp' (Ideal.Quotient.mk (Ideal.span {f})) e.toRingHom phi hphi).hom.app
    (ModuleCat.of B B) ≫
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).map
        (ModuleCat.restrictScalarsIsoOfEquiv e).hom

lemma originalQuotientUnitCoordinate_apply212
    {R B : Type u} [CommRing R] [CommRing B] (f : R)
    (e : (R ⧸ Ideal.span {f}) ≃+* B)
    (phi : R →+* B) (hphi : phi = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {f})))
    (b : B) : (originalQuotientUnitCoordinate212 f e phi hphi).hom b = e.symm b := rfl

/-- The202 WHOLE-sequence first coordinate equals the actual canonical
unit coordinate composed with its original first-module frame. -/
theorem quotientWholePrincipal_firstCoordinate212
    {R B : Type u} [CommRing R] [CommRing B] (f : R)
    (e : (R ⧸ Ideal.span {f}) ≃+* B)
    (phi : R →+* B) (hphi : phi = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {f})))
    (W : ShortComplex (ModuleCat B)) (t : B) (ht : t ∈ B⁰)
    (a : W ≅ pointCartierYonedaCoefficientComplex t) :
    let q := Ideal.Quotient.mk (Ideal.span {f})
    let Q := ModuleCat.restrictScalars q
    let eta := ModuleCat.restrictScalarsComp' q e.toRingHom phi hphi
    let aC := quotientWholePrincipalIso202 f e W t ht a
    let e₁ := (ShortComplex.π₁ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso aC
    (eta.app W.X₁).hom ≫ Q.map e₁.hom =
      (ModuleCat.restrictScalars phi).map a.hom.τ₁ ≫
        originalQuotientUnitCoordinate212 f e phi hphi := by
  dsimp only
  let q := Ideal.Quotient.mk (Ideal.span {f})
  let Q := ModuleCat.restrictScalars q
  let eta := ModuleCat.restrictScalarsComp' q e.toRingHom phi hphi
  change (eta.app W.X₁).hom ≫ Q.map (quotientWholePrincipalIso202 f e W t ht a).hom.τ₁ = _
  rw [quotientWholePrincipalIso_first_hom202]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Ordinary categorical cancellation through an actual quotient epi and
an actual whole endpoint Iso. The geometric caller derives the square. -/
lemma originalUnitQuotientCoordinate_cancel212
    {C : Type*} [Category C] {U M N T V : C}
    (q : U ⟶ M) [Epi q] (eta : M ≅ N)
    (v : M ⟶ T) (a : T ⟶ V) (b : N ⟶ V)
    (h : q ≫ v ≫ a = q ≫ eta.hom ≫ b) : eta.inv ≫ v ≫ a = b := by
  apply (cancel_epi (q ≫ eta.hom)).mp
  simpa only [Category.assoc, eta.hom_inv_id_assoc] using h

end PfaffianDescent
