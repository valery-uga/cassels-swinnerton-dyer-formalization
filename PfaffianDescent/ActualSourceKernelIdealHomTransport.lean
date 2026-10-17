import PfaffianDescent.SurjectiveAffineActualIdealTildeIso

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

/-- Genuine raw ideal inclusion square with internally derived source-kernel
transport. Result inference avoids the duplicated expected-equation conversion. -/
def actualSourceKernelIdealHomTransport
    {X Z Z' : Scheme.{u}} (e : Z ≅ Z') (i : Z' ⟶ X) :=
  @idealModuleTransport_hom_toUnit X (e.hom ≫ i).ker i.ker
    (Scheme.Hom.ker_comp_of_isIso e.hom i)

end PfaffianDescent
