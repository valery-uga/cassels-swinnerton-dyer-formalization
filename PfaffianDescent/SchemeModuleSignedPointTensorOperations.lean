import PfaffianDescent.SchemeModuleTensor
import PfaffianDescent.SchemeModuleInternalHomSheaf
import Mathlib.Topology.JacobsonSpace

/-! The literal geometric signed point tensor step and finite fold.
These SAME definitions are shared by the canonical word geometry and
cohomology iteration. No Ext/finiteness/Euler theorem is needed to form
these actual ideal/dual tensors. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open IdealSheafDataModule
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- One actual point tensor operation: positive dual tensor or negative
ideal tensor. Every ideal and dual is the original geometric construction. -/
def schemeModuleSignedClosedPointTensor (op : closedPoints X × Bool) (L : X.Modules) : X.Modules :=
  match op with
  | (P, true) =>
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    schemeModuleTensor L (SchemeModuleInternalHom.dual (closedImmersionModule i))
  | (P, false) =>
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    schemeModuleTensor (closedImmersionModule i) L

/-- Literal finite successive tensor operations in the specified order. -/
def schemeModuleIteratedSignedClosedPointTensor
    (L : X.Modules) (ops : List (closedPoints X × Bool)) : X.Modules :=
  ops.foldl (fun T op => schemeModuleSignedClosedPointTensor op T) L

end PfaffianDescent.Coray
