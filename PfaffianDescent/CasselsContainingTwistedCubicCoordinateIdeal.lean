import PfaffianDescent.CasselsPerfectQuarticCoordinates
import PfaffianDescent.CorayPerfectQuinticCoordinates
import PfaffianDescent.AlgebraVectorCoordinateChange
import PfaffianDescent.AlgebraVectorHomogeneous
import PfaffianDescent.ProjectiveLinearCoordinateAmbientSquare
import PfaffianDescent.QuarticTwistedCubicGeometricPresentation

/-! SOURCE ONLY. Literal original-coordinate containing twisted cubic for
Cassels degree-four/five points. Ground matrix, common scalar and curve ideal
are constructed; no containing curve or residual-cycle conclusion is supplied. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators MatrixGroups
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The entire original-coordinate curve ideal, pulled back along the
original matrix sending the power tuple to the original point coordinates. -/
def casselsContainingTwistedCubicIdeal
    {K : Type u} [Field K] (M : Mat K 4) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) :=
  (QuarticNet.standardTwistedCubicHomogeneousIdeal (K := K)).comap
    (linearCoordinateChangeAmbientGradedHom M)

/-- Invertibility gives the ground embedded twisted-cubic presentation of
this exact ideal, with no ideal-equality or presentation certificate supplied. -/
theorem casselsContainingTwistedCubicIdeal_groundPresentation
    {K : Type u} [Field K] (M : Mat K 4) (hM : IsUnit M.det) :
    QuarticNet.GroundTwistedCubicPresentation (casselsContainingTwistedCubicIdeal M) := by
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr hM
  obtain ⟨U, hU⟩ := hunit
  refine ⟨U, ?_⟩
  rw [hU]
  change ((QuarticNet.standardTwistedCubicIdeal K).comap
      (linearSubstitution M).toRingHom).map (linearSubstitution M).toRingHom = _
  exact Ideal.map_comap_of_surjective (linearSubstitution M).toRingHom
    (linearSubstitutionEquiv M hM).surjective (QuarticNet.standardTwistedCubicIdeal K)

/-- The actual standard homogeneous generators vanish on the literal powers
of any element, without a separability or field-degree premise. -/
theorem standardTwistedCubicIdeal_le_powerTupleIdeal
    {K L : Type u} [Field K] [Field L] [Algebra K L] (a : L) :
    QuarticNet.standardTwistedCubicIdeal K ≤
      algebraVectorIdeal (K := K) (fun i : Fin 4 => a ^ (i : ℕ)) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply (mem_algebraVectorIdeal_of_homogeneous
    (fun i : Fin 4 => a ^ (i : ℕ))
    (QuarticNet.standardTwistedCubicGenerators K i)
    (QuarticNet.standardTwistedCubicGenerators_homogeneous K i)).mpr
  fin_cases i <;> simp [QuarticNet.standardTwistedCubicGenerators] <;> ring

/-- The constructed curve ideal is contained in the SAME original tuple's
homogeneous line kernel, including nonhomogeneous equations in that ideal. -/
theorem casselsContainingTwistedCubicIdeal_le_originalCoordinateIdeal
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (a v : L) (hv : v ≠ 0) (M : Mat K 4) (p : Vec L 4)
    (hp : p = v • (M.map (algebraMap K L)).mulVec
      (fun i : Fin 4 => a ^ (i : ℕ))) :
    (casselsContainingTwistedCubicIdeal M).toIdeal ≤ algebraVectorIdeal (K := K) p := by
  let u : Lˣ := Units.mk0 v hv
  have hscaled : algebraVectorIdeal (K := K) p =
      algebraVectorIdeal (K := K)
        ((M.map (algebraMap K L)).mulVec (fun i : Fin 4 => a ^ (i : ℕ))) := by
    rw [hp]
    exact algebraVectorIdeal_unit_smul u _
  rw [hscaled, algebraVectorIdeal_linearSubstitution]
  exact Ideal.comap_mono (standardTwistedCubicIdeal_le_powerTupleIdeal a)

/-- Every equation in the homogeneous line kernel vanishes on the original
coordinate tuple; this does not identify ordinary affine evaluation with the
homogeneous ideal in the reverse direction. -/
theorem algebraVectorIdeal_eval_zero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : Vec L 4) (f : MvPolynomial (Fin 4) K)
    (hf : f ∈ algebraVectorIdeal (K := K) p) :
    f.eval₂ (algebraMap K L) p = 0 := by
  have hcomp : (MvPolynomial.aeval (fun _ : Unit => (1 : L))).toRingHom.comp
      (algebraLineHom (K := K) p).toRingHom = (MvPolynomial.aeval p).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [algebraLineHom_C]
    · intro i
      simp [algebraLineHom_X]
  have h := DFunLike.congr_fun hcomp f
  change MvPolynomial.aeval (fun _ : Unit => (1 : L)) (algebraLineHom p f) =
    MvPolynomial.aeval p f at h
  have hzero : algebraLineHom (K := K) p f = 0 := hf
  rw [hzero, map_zero] at h
  exact h.symm

/-- Both literal Cassels degrees construct the primitive element, original
invertible matrix and one common nonzero scalar over the PERFECT base. -/
theorem perfectField_degree_four_or_five_power_coordinates
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : finrank K L = 4 ∨ finrank K L = 5)
    (p : Vec L 4) (hp : LinearIndependent K p) :
    ∃ a : L, (minpoly K a).natDegree = finrank K L ∧
      ∃ v : L, v ≠ 0 ∧ ∃ M : Mat K 4, IsUnit M.det ∧
        p = v • (M.map (algebraMap K L)).mulVec
          (fun i : Fin 4 => a ^ (i : ℕ)) := by
  rcases hdim with h4 | h5
  · obtain ⟨a, ha, M, hM, hcoord⟩ := perfectField_independentQuarticCoordinates h4 p hp
    refine ⟨a, ha.trans h4.symm, 1, one_ne_zero, M,
      (Matrix.isUnit_iff_isUnit_det M).mp
        (Matrix.mulVec_injective_iff_isUnit.mp hM), ?_⟩
    simpa only [one_smul] using hcoord
  · obtain ⟨a, ha, v, hv, M, hM, hcoord⟩ :=
      Coray.perfectField_independentQuinticCoordinates h5 p hp
    exact ⟨a, ha.trans h5.symm, v, hv, M,
      (Matrix.isUnit_iff_isUnit_det M).mp
        (Matrix.mulVec_injective_iff_isUnit.mp hM), hcoord⟩

/-- Literal containing-curve ideal: no supplied ground curve, desired ideal
containment, or degree-nine/rational-point conclusion. -/
theorem perfectField_independent_degree_four_or_five_exists_containing_twistedCubicIdeal
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : finrank K L = 4 ∨ finrank K L = 5)
    (p : Vec L 4) (hp : LinearIndependent K p) :
    ∃ B : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
      QuarticNet.GroundTwistedCubicPresentation B ∧
      ∀ f ∈ B.toIdeal, f.eval₂ (algebraMap K L) p = 0 := by
  obtain ⟨a, ha, v, hv, M, hM, hcoord⟩ :=
    perfectField_degree_four_or_five_power_coordinates hdim p hp
  refine ⟨casselsContainingTwistedCubicIdeal M,
    casselsContainingTwistedCubicIdeal_groundPresentation M hM, ?_⟩
  intro f hf
  exact algebraVectorIdeal_eval_zero p f
    (casselsContainingTwistedCubicIdeal_le_originalCoordinateIdeal a v hv M p hcoord hf)

end PfaffianDescent
