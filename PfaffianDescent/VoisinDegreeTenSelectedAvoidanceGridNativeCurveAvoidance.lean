import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridNativeKernelFour
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridExtendedCurveContradiction

/-! Native cubic-kernel curve avoidance follows from exact ordered kernel
transport and the literal finite triple witness. -/
noncomputable section
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_nativeCubicKernel_noFixedHeightTwoPrime_of_orderedTransport
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (x : Fin 4 → A) (hA : finrank K A ≤ 16)
    {W : Type*} [AddCommGroup W] [Module L W]
    (T : homogeneousSubmodule (Fin 4) L 3 →ₗ[L] W)
    (hT : finrank L (LinearMap.ker T) = 4)
    (htransport : ∀ (s : homogeneousSubmodule (Fin 4) K 3),
      s ∈ LinearMap.ker (homogeneousSectionRestriction x 3) →
      voisinDegreeTenSelectedAvoidance_mapCubicSection (L := L) s ∈ LinearMap.ker T)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q r : homogeneousSubmodule (Fin 4) L 3)
    (hq : q ∈ LinearMap.ker T) (hr : r ∈ LinearMap.ker T)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap K L)) q.1 r.1 (hp.map (algebraMap K L)) q.2 r.2))] :
    ¬ ∃ C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
      C.toIdeal.IsPrime ∧ C.toIdeal.height = 2 ∧ p ∈ C.toIdeal ∧
      (∀ (s : homogeneousSubmodule (Fin 4) K 3),
        s ∈ LinearMap.ker (homogeneousSectionRestriction x 3) → s.1 ∈ C.toIdeal) := by
  rintro ⟨C, hCprime, hCheight, hpC, hcontains⟩
  obtain ⟨s, hsli, hsker⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_four_independent_nativeCubicKernelMembers x hA
  have hspan := voisinDegreeTenSelectedAvoidance_cubicBasis_span_kernel_after_scalarExtension
    (L := L) s hsli T (fun i => htransport (s i) (hsker i)) hT
  let D := HomogeneousIdeal.map (ambientCoefficientGradedRingHom (algebraMap K L)) C
  let H : Submodule L (homogeneousSubmodule (Fin 4) L 3) :=
    (Submodule.restrictScalars L D.toIdeal).comap
      (homogeneousSubmodule (Fin 4) L 3).subtype
  have hspanH : Submodule.span L (Set.range (fun i =>
      voisinDegreeTenSelectedAvoidance_mapCubicSection (L := L) (s i))) ≤ H := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (s i).1.map (algebraMap K L) ∈ D.toIdeal
    exact Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap K L))
      (hcontains (s i) (hsker i))
  rw [hspan] at hspanH
  have hqD : q.1 ∈ D.toIdeal := hspanH hq
  have hrD : r.1 ∈ D.toIdeal := hspanH hr
  have hpD : p.map (algebraMap K L) ∈ D.toIdeal :=
    Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap K L)) hpC
  exact voisinDegreeTenSelectedAvoidance_finiteTriple_not_contained_in_extendedHeightTwoPrime
    (p.map (algebraMap K L)) q.1 r.1 (hp.map (algebraMap K L)) q.2 r.2
    C hCprime hCheight ⟨hpD, hqD, hrD⟩

end PfaffianDescent
