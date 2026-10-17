import PfaffianDescent.VoisinDegreeElevenSerreIncidencePulledSerre
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Actual affine inverse-image cover of the pulled Serre extension -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidencePulledCover
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f] [IsAffineHom f] {N : X.Modules}
    (e : SerreExtensionData X N) (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) :
    SerreExtensionData.SerreExtensionRankTwoAffineCover (serreIncidencePulledSerre f e C) where
  ι := C.ι
  U := fun i => f ⁻¹ᵁ C.U i
  covers := f.iSup_preimage_eq_top C.covers
  affine i := IsAffineOpen.preimage (show IsAffineOpen (C.U i) from C.affine i) f
  overlapAffine i j := IsAffineOpen.preimage (show IsAffineOpen (C.U i ⊓ C.U j) from C.overlapAffine i j) f
  trivialization i := serreIncidencePulledFreeOverIso f
    (show X.Modules from e.E) (C.U i) (ULift.{u} (Fin 2)) (C.trivialization i)

end PfaffianDescent
