import PfaffianDescent.SerreActualCubicGroundFamilyOldGoodSeedNewMarkedGoodOpen

/-! Keep the old-good to literal-new-good proof at its checked generic
coefficient-family endpoint. The original degree-eleven support and rank-chart
metadata are unused by this transport, so they do not enter this proof alias. -/

noncomputable section
namespace PfaffianDescent

/-- The same actual old seed, ground parameter, coefficient Serre module and
literal transported marked sections as the checked good-seed constructor.
Finiteness and properness are derived internally from the old good seed. -/
@[irreducible]
def serreActualCubicGroundFamily_oldSelectedSeed_nativeNewGoodMembership :=
  @serreActualCubicGroundFamily_oldGoodSeed_toNewMarkedSeed_mem_goodOpen

end PfaffianDescent
