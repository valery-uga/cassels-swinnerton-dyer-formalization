import AllCharacteristics.PrescribedLaurentPencilDegreeOne
import AllCharacteristics.PrescribedLaurentPencilProperSpecialization
import AllCharacteristics.CubicSmoothing
import AllCharacteristics.SmoothCubicReference

/-! SOURCE ONLY / UNVERIFIED. The literal pencil method uses only the
stated smooth-cubic theorem over k((t)), with the actual prescribed-point
lift/degree, actual line intersection, Bézout and proper specialization. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory IsLocalRing
open HomogeneousProjective
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem originalSmoothPoint_section_of_literalLaurentPencil
    (smoothGeneric : SmoothCubicZeroCyclePointFor (LaurentSeries k))
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hq : q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (hsm : q (closedPoint L) ∈ (hypersurfaceToBase p hp).smoothLocus)
    (hdegree : Nat.Coprime (Module.finrank k L) 3) :
    ∃ r : Spec (.of k) ⟶ hypersurface p hp,
      r ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨g, hg, hg0, hgs⟩ := smoothCubicReferenceFor k
  letI : Smooth (hypersurfaceToBase g hg) := hgs
  obtain ⟨w, hw⟩ := prescribedOriginalSmoothPoint_generic_degreeOne_cycle
    p g hp hg hp0 hg0 q hq hsm hdegree
  obtain ⟨a, ha⟩ := smoothGeneric (prescribedLaurentGenericEquation p g)
    (prescribedLaurentGenericEquation_homogeneous hp hg)
    (prescribedLaurentGenericEquation_ne_zero hg0)
    (prescribedLaurentGenericEquation_smooth hp hg hg0) w hw
  exact prescribedLaurentGenericSection_specializes_original p g hp hg a ha

end AllCharacteristics
