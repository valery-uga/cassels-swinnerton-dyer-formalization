import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Ordinary module pullback commutes with literal open restriction through
its native composition and open-immersion comparison isomorphisms. -/
def cubicClosedPointSerreTensorStalk_pullbackRestrictNatIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ U) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f.resLE U V hV) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback V.ι) ≪≫
    Scheme.Modules.pullbackComp V.ι f ≪≫
    Scheme.Modules.pullbackCongr (f.resLE_comp_ι hV).symm ≪≫
    (Scheme.Modules.pullbackComp (f.resLE U V hV) U.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
      (Scheme.Modules.pullback (f.resLE U V hV))

/-- A map invertible on an actual target open remains invertible after
actual pullback and restriction to its preimage, without flatness hypotheses. -/
theorem cubicClosedPointSerreTensorStalk_restrict_pullbackMap_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ U)
    {M N : Y.Modules} (g : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map g)] :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      ((Scheme.Modules.pullback f).map g)) := by
  let n := cubicClosedPointSerreTensorStalk_pullbackRestrictNatIso f U V hV
  let A := Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor V.ι
  let B := Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f.resLE U V hV)
  have h : A.map g ≫ n.hom.app N = n.hom.app M ≫ B.map g := n.hom.naturality g
  letI : IsIso (B.map g) := by
    dsimp only [B, Functor.comp_map]
    infer_instance
  letI : IsIso (A.map g ≫ n.hom.app N) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right (A.map g) (n.hom.app N)

end PfaffianDescent
