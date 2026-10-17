import PfaffianDescent.SchemeBaseScalarPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/- SOURCE ONLY / UNVERIFIED. Genuine sheafification of the relative
Kaehler presheaf. Its universal property is proved against EVERY actual
module sheaf, not postulated as a chart-comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable {k : Type u} [CommRing k] {X : Scheme.{u}}

/-- The actual relative differential scheme-module. -/
def schemeRelativeDifferentials (g : X ⟶ Spec (CommRingCat.of k)) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (schemeRelativeDifferentialsPresheaf g)

/-- The universal relative differential sheaf factorization. The harmless
restrictScalars by the identity is kept explicit to avoid hiding the
sheafification adjunction's actual target presheaf. -/
theorem schemeRelativeDifferentials_universal
    (g : X ⟶ Spec (CommRingCat.of k)) (N : X.Modules)
    (d : ((PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj N.val).Derivation' (schemeBaseScalarPresheafMap g)) :
    ∃! f : schemeRelativeDifferentials g ⟶ N,
      (schemeRelativeDifferentialsPresheafDerivation g).postcomp
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).homEquiv
            (schemeRelativeDifferentialsPresheaf g) N f) = d := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let e := adj.homEquiv (schemeRelativeDifferentialsPresheaf g) N
  let h := schemeRelativeDifferentialsPresheafUniversal g
  refine ⟨e.symm (h.desc d), ?_, ?_⟩
  · change (schemeRelativeDifferentialsPresheafDerivation g).postcomp
      (e (e.symm (h.desc d))) = d
    exact (congrArg (fun t =>
      (schemeRelativeDifferentialsPresheafDerivation g).postcomp t)
      (e.apply_symm_apply (h.desc d))).trans (h.fac d)
  · intro f hf
    apply e.injective
    exact (h.postcomp_injective (e f) (h.desc d)
      (hf.trans (h.fac d).symm)).trans (e.apply_symm_apply (h.desc d)).symm

end PfaffianDescent
