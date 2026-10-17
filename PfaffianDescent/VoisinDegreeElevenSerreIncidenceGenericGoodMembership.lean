import PfaffianDescent.VoisinDegreeElevenSerreIncidencePlaneGenericGoodParameter
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSeedFibreProperties

/-! # The selected generic parameter lies in both actual geometric opens -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidencePlane_exists_generic_good_open_parameter
    {Z I B : Scheme.{u}} [IsAffine B] [IsIntegral B]
    (zero : Z ⟶ I) [IsProper zero] (W : I.Opens) (π : I ⟶ B)
    (e : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≅ I)
    (he : e.hom ≫ π = toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≫ B.isoSpec.inv)
    (hπ : IsOpenMap π) (i : I) (hi : (zero ⁻¹' {i}).Finite) (hiW : i ∈ W)
    [Infinite (B.residueField (genericPoint B))] :
    ∃ s : Spec (B.residueField (genericPoint B)) ⟶ I,
      s ≫ π = B.fromSpecResidueField (genericPoint B) ∧
      s (IsLocalRing.closedPoint (B.residueField (genericPoint B))) ∈
        serreIncidenceGoodOpen zero W ∧ IsFinite (pullback.snd zero s) := by
  obtain ⟨s, hs, hW, hf⟩ := serreIncidencePlane_exists_generic_good_parameter
    zero W π e he hπ i hi hiW
  letI : IsFinite (pullback.snd zero s) := hf
  let x := s (IsLocalRing.closedPoint (B.residueField (genericPoint B)))
  letI : Finite (zero.fiber x) :=
    cubicClosedPointSerreFiniteZeroResidual_seed_residue_fibre_finite zero s
  letI : Finite (zero ⁻¹' {x} : Set Z) := (zero.fiberHomeo x).finite_iff.mp inferInstance
  have hp : (zero ⁻¹' {x}).Finite := Set.toFinite _
  exact ⟨s, hs, ⟨cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre
    zero x hp, hW⟩, hf⟩

end PfaffianDescent
