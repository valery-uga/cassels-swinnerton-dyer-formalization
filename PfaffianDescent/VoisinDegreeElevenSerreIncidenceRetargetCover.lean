import PfaffianDescent.SerreExtensionFoundation

/-! # Native rank-two cover retained under actual quotient identification -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceRetargetCover
    {X : Scheme.{u}} {M N : X.Modules} (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e) (q : M ≅ N) :
    SerreExtensionData.SerreExtensionRankTwoAffineCover (e.retarget q) where
  ι := C.ι
  U := C.U
  covers := C.covers
  affine := C.affine
  overlapAffine := C.overlapAffine
  trivialization := C.trivialization

end PfaffianDescent
