import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProjectivePlane
import Mathlib.AlgebraicGeometry.Fiber

/-! # Finite zero on the actual generic incidence fibre -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The finite-zero open meets the scheme-theoretic generic incidence fibre.
The witness is transported through the actual fibre homeomorphism. -/
theorem serreIncidenceFiniteZero_genericFibre_nonempty
    {Z I B : Scheme.{u}} (zero : Z ⟶ I) [IsProper zero]
    (π : I ⟶ B) [IsIntegral B] (hπ : IsOpenMap π)
    (i : I) (hi : (zero ⁻¹' {i}).Finite) :
    (((π.fiberι (genericPoint B)) ⁻¹ᵁ
      cubicClosedPointSerreFiniteZeroResidual_goodOpen zero) :
      Set (π.fiber (genericPoint B))).Nonempty := by
  obtain ⟨j, hj, hjV⟩ := serreIncidenceFiniteZeroImage_genericPoint zero π hπ i hi
  let jF : π.fiber (genericPoint B) :=
    (π.fiberHomeo (genericPoint B)).symm ⟨j, hj⟩
  refine ⟨jF, ?_⟩
  change π.fiberι (genericPoint B) jF ∈
    cubicClosedPointSerreFiniteZeroResidual_goodOpen zero
  simpa only [jF, Scheme.Hom.fiberι_fiberHomeo_symm] using hjV

/-- An actual projective-plane isomorphism of the generic kernel fibre
transfers that nonempty finite-zero open to projective parameters. -/
theorem serreIncidenceFiniteZero_genericPlane_nonempty
    {Z I B : Scheme.{u}} (zero : Z ⟶ I) [IsProper zero]
    (π : I ⟶ B) [IsIntegral B] (hπ : IsOpenMap π)
    (i : I) (hi : (zero ⁻¹' {i}).Finite)
    (e : serreKernelProjectivePlane (B.residueField (genericPoint B)) ≅
      π.fiber (genericPoint B)) :
    (((e.hom ≫ π.fiberι (genericPoint B)) ⁻¹ᵁ
      cubicClosedPointSerreFiniteZeroResidual_goodOpen zero) :
      Set (serreKernelProjectivePlane (B.residueField (genericPoint B)))).Nonempty := by
  obtain ⟨j, hj⟩ := serreIncidenceFiniteZero_genericFibre_nonempty zero π hπ i hi
  refine ⟨e.inv j, ?_⟩
  change (e.hom ≫ π.fiberι (genericPoint B)) (e.inv j) ∈
    cubicClosedPointSerreFiniteZeroResidual_goodOpen zero
  rw [Scheme.Hom.comp_apply]
  have h : e.hom (e.inv j) = j := by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl
  rw [h]
  exact hj

end PfaffianDescent
