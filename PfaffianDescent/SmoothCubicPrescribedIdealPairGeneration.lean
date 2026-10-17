import AllCharacteristics.FlatPrescribedIdealPairGeneration
import PfaffianDescent.SmoothCubicClosedPointNativeLCI164

/-! SOURCE ONLY167. Original smooth cubic / original closed-point caller.
Constructs a two-generator presentation of the given ENTIRE deformation
ideal using164 internally. Regularity is proved on the ORIGINAL special
fiber only, not silently promoted to the ambient deformation. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u v w
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A prescribed flat ideal deformation of the ORIGINAL closed point
admits lifts inside the same ideal generating it entirely. The original
special-fiber pair is a native regular sequence derived from smoothness. -/
theorem smoothCubic_originalClosedPoint_prescribedIdeal_pair_generators167
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (P : closedPoints (hypersurface p hp))
    {R : Type v} {A : Type w} [CommRing R] [CommRing A] [Algebra R A]
    (π : A →+* (hypersurface p hp).presheaf.stalk P.1)
    (hπ : Function.Surjective π) (I : Ideal R) (hI : IsNilpotent I)
    (hker : RingHom.ker π = I.map (algebraMap R A))
    (J : Ideal A) [Module.Flat R (A ⧸ J)]
    (hreduce : J.map π = RingHom.ker (((hypersurface p hp).residue P.1).hom)) :
    ∃ f g : A, f ∈ J ∧ g ∈ J ∧
      J = Ideal.span ({f, g} : Set A) ∧
      RingTheory.Sequence.IsRegular ((hypersurface p hp).presheaf.stalk P.1)
        [π f, π g] ∧
      Ideal.span ({π f, π g} : Set ((hypersurface p hp).presheaf.stalk P.1)) =
        RingHom.ker (((hypersurface p hp).residue P.1).hom) := by
  obtain ⟨f₀, g₀, hreg, hspan⟩ :=
    smoothCubic_originalClosedPoint_residueKernel_regularSequence164 p hp hp0 P
  obtain ⟨f, g, hf, hg, hff, hgg, hJ⟩ :=
    AllCharacteristics.exists_prescribedIdeal_pair_lifts_of_nilpotent_reduction167
      π hπ I hI hker J f₀ g₀ (hreduce.trans hspan.symm)
  refine ⟨f, g, hf, hg, hJ, ?_, ?_⟩
  · simpa only [hff, hgg] using hreg
  · simpa only [hff, hgg] using hspan

end PfaffianDescent
