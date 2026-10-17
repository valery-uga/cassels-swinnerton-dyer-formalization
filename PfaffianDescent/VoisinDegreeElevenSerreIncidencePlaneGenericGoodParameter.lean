import PfaffianDescent.VoisinDegreeElevenSerreIncidencePlaneFieldPoint
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGoodOpen

/-! # Actual plane incidence produces a same-field finite-zero generic parameter in the marked open -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidencePlane_exists_generic_good_parameter
    {Z I B : Scheme.{u}} [IsAffine B] [IsIntegral B]
    (zero : Z ⟶ I) [IsProper zero] (W : I.Opens) (π : I ⟶ B)
    (e : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≅ I)
    (he : e.hom ≫ π = toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≫ B.isoSpec.inv)
    (hπ : IsOpenMap π) (i : I) (hi : (zero ⁻¹' {i}).Finite) (hiW : i ∈ W)
    [Infinite (B.residueField (genericPoint B))] :
    ∃ s : Spec (B.residueField (genericPoint B)) ⟶ I,
      s ≫ π = B.fromSpecResidueField (genericPoint B) ∧
      s (IsLocalRing.closedPoint (B.residueField (genericPoint B))) ∈ W ∧
      IsFinite (pullback.snd zero s) := by
  let c := B.fromSpecResidueField (genericPoint B)
  let v := serreIncidencePlaneFieldPointIso π e he c
  let frame := v.hom ≫ pullback.fst π c
  have hf : frame ≫ π = serreKernelProjectivePlaneToBase
      (B.residueField (genericPoint B)) ≫ c :=
    serreIncidencePlaneFieldPointIso_frame π e he c
  have hne : ((frame ⁻¹ᵁ serreIncidenceGoodOpen zero W) :
      Set (serreKernelProjectivePlane (B.residueField (genericPoint B)))).Nonempty := by
    obtain ⟨j, hj⟩ := serreIncidenceGoodOpen_genericFibre_nonempty zero W π hπ i hi hiW
    refine ⟨v.inv j, ?_⟩
    change (v.hom ≫ pullback.fst π c) (v.inv j) ∈ serreIncidenceGoodOpen zero W
    rw [Scheme.Hom.comp_apply]
    have hv : v.hom (v.inv j) = j := by
      rw [← Scheme.Hom.comp_apply, v.inv_hom_id]
      rfl
    rw [hv]
    exact hj
  exact serreIncidenceProjectivePlane_exists_good_parameter_over
    (F := B.residueField (genericPoint B)) zero W π c frame hf hne

end PfaffianDescent
