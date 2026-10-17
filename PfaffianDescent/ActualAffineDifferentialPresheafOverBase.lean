import PfaffianDescent.SchemeBaseScalarPresheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde

/- SOURCE ONLY / UNVERIFIED. The actual relative-differential presheaf,
forgotten using the INSTALLED canonical top-to-open actions over R.
No native/bundled algebra equality is silently treated as defeq. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]

/-- The SAME actual differential presheaf, with its canonical R-actions
and actual restriction maps supplied by the installed forgetful functor. -/
def actualAffineDifferentialPresheafOverBase :
    (Spec (CommRingCat.of R)).Opensᵒᵖ ⥤ ModuleCat R :=
  ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
    (CategoryTheory.Limits.initialOpOfTerminal CategoryTheory.Limits.isTerminalTop)).obj
      (schemeRelativeDifferentialsPresheaf
        (Spec.map (CommRingCat.ofHom (algebraMap k R))))) ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- The top-to-basis factorization used by abstract localization uniqueness
is a true actual restriction identity, derived internally from the functor. -/
lemma actualAffineDifferentialPresheafOverBase_top_restriction
    (U V : (Spec (CommRingCat.of R)).Opens) (hVU : V ≤ U) :
    (actualAffineDifferentialPresheafOverBase (k := k) (R := R)).map U.leTop.op ≫
        (actualAffineDifferentialPresheafOverBase (k := k) (R := R)).map
          (homOfLE hVU).op =
      (actualAffineDifferentialPresheafOverBase (k := k) (R := R)).map V.leTop.op := by
  let F := actualAffineDifferentialPresheafOverBase (k := k) (R := R)
  exact (F.map_comp U.leTop.op (homOfLE hVU).op).symm.trans
    (congrArg (fun f => F.map f) (Subsingleton.elim _ _))

end PfaffianDescent
