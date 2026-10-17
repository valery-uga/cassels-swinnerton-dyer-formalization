import PfaffianDescent.SchemeBaseScalarPresheaf
import Mathlib.AlgebraicGeometry.StructureSheaf

/- SOURCE ONLY / UNVERIFIED. Constants in the genuine scheme construction
agree with the usual k -> R -> Gamma(U) map on every actual affine open. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma affineSchemeBaseScalarPresheafMap_app
    (U : (Spec (CommRingCat.of R)).Opens) :
    letI : Algebra R Γ(Spec (CommRingCat.of R), U) := inferInstanceAs
      (Algebra R ((Spec.structureSheaf R).obj.obj (op U)))
    (schemeBaseScalarPresheafMap
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))).app (op U) =
        CommRingCat.ofHom
          ((algebraMap R Γ(Spec (CommRingCat.of R), U)).comp (algebraMap k R)) := by
  dsimp only
  letI : Algebra R Γ(Spec (CommRingCat.of R), U) := inferInstanceAs
    (Algebra R ((Spec.structureSheaf R).obj.obj (op U)))
  change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop ≫
      (Spec (CommRingCat.of R)).presheaf.map U.leTop.op = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Scheme.ΓSpecIso_inv]
  rfl

end PfaffianDescent
