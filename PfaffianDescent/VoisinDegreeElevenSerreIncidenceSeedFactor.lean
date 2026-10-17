import PfaffianDescent.VoisinDegreeElevenSerreIncidenceClosedFamily
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualIdealCover

/-! # Literal simultaneous marked zero lifts construct an actual incidence seed -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable {S B X P Z T : Scheme.{u}}
variable (b : B ⟶ S) (x : X ⟶ S) (p : P ⟶ S)
variable (marked : Fin 3 → (B ⟶ X)) (hm : ∀ i, marked i ≫ x = b)
variable (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]
variable (a : T ⟶ pullback b p) (lift : Fin 3 → (T ⟶ Z))
variable (hl : ∀ i, lift i ≫ zero = a ≫ fixedLinearSystemIncidenceMap b x p marked hm i)

include lift hl in
theorem serreIncidenceSeed_kernel_le :
    (serreThreePointSectionIncidenceToProduct b x p marked hm zero).ker ≤ a.ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι]
  apply iSup_le
  intro i
  let inc := fixedLinearSystemIncidenceMap b x p marked hm i
  let w := pullback.lift (lift i) a (hl i)
  have hw : w ≫ pullback.snd zero inc = a := pullback.lift_snd _ _ _
  rw [← cubicClosedPointSerreFiniteZeroResidual_pullback_snd_kernel zero inc, ← hw]
  exact Scheme.Hom.le_ker_comp w (pullback.snd zero inc)

def serreIncidenceSeed : T ⟶ serreThreePointSectionIncidence b x p marked hm zero :=
  IsClosedImmersion.lift (serreThreePointSectionIncidenceToProduct b x p marked hm zero) a
    (serreIncidenceSeed_kernel_le b x p marked hm zero a lift hl)

@[reassoc (attr := simp)]
theorem serreIncidenceSeed_toProduct :
    serreIncidenceSeed b x p marked hm zero a lift hl ≫
      serreThreePointSectionIncidenceToProduct b x p marked hm zero = a :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc]
theorem serreIncidenceSeed_toParameters :
    serreIncidenceSeed b x p marked hm zero a lift hl ≫
      serreThreePointSectionIncidenceToParameters b x p marked hm zero = a ≫ pullback.snd b p := by
  simp only [serreThreePointSectionIncidenceToParameters, ← Category.assoc,
    serreIncidenceSeed_toProduct]

@[reassoc]
theorem serreIncidenceSeed_toConfiguration :
    serreIncidenceSeed b x p marked hm zero a lift hl ≫
      serreThreePointSectionIncidenceToConfiguration b x p marked hm zero = a ≫ pullback.fst b p := by
  simp only [serreThreePointSectionIncidenceToConfiguration, ← Category.assoc,
    serreIncidenceSeed_toProduct]

end
end PfaffianDescent
