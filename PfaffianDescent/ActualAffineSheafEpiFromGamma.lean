import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/- SOURCE ONLY / UNVERIFIED. Gamma surjectivity detects Epi with an actual
quasicoherent TARGET. The counit is a legitimate conditional auxiliary
argument, not assumed for all affine sheaves or supplied by final caller. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

theorem actualAffineSheafMap_epi_of_gamma_surjective
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (f : M ⟶ N) [IsIso N.fromTildeΓ]
    (hsurj : Function.Surjective ((moduleSpecΓFunctor (R := R)).map f)) : Epi f := by
  let F := moduleSpecΓFunctor (R := R)
  letI : Epi (F.map f) := (ModuleCat.epi_iff_surjective _).2 hsurj
  have h : M.fromTildeΓ ≫ f = (tilde.functor R).map (F.map f) ≫ N.fromTildeΓ :=
    ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality f).symm
  letI : Epi (M.fromTildeΓ ≫ f) := h.symm ▸ inferInstance
  exact epi_of_epi M.fromTildeΓ f

end PfaffianDescent
