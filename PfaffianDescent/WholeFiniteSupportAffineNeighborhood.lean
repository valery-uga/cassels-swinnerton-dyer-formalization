import PfaffianDescent.NilpotentCartesianFieldPointSupport176
import PfaffianDescent.ProjectiveFiniteFamilyHomogeneousWholeOpenCover
import PfaffianDescent.NativeOpenContainedFiniteFlatPointEquiv315

/-!
Whole-support affine neighborhood constructions for arbitrary finite-flat
families, including nonreduced families with several support points.
These neighborhood lemmas are used before the Hilbert--Burch deformation
construction; they do not require a determinantal presentation.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
universe u v
set_option autoImplicit false

/-- Nilpotent coefficient reduction preserves the WHOLE image of a
Cartesian family.  The special family can be arbitrary: no singleton,
reducedness, closed immersion, or finite-flat hypothesis is needed. -/
theorem nilpotentCartesianFamily_range001
    {B K : Type u} [CommRing B] [CommRing K]
    {X X0 Z Z0 : Scheme.{u}}
    (F : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b)
    (hnil : IsNilpotent (RingHom.ker b))
    (d : X0 ⟶ X) (F0 : X0 ⟶ Spec (.of K))
    (H0 : IsPullback d F0 F (Spec.map (CommRingCat.ofHom b)))
    (i : Z ⟶ X) (r : Z0 ⟶ Z) (i0 : Z0 ⟶ X0)
    (H : IsPullback r i0 i d) :
    Set.range i = d '' Set.range i0 := by
  have HZ := H.paste_vert H0
  letI : Surjective r := surjective_cartesianFamilyFiber_of_nilpotent_kernel176
    (i ≫ F) b hb hnil r (i0 ≫ F0) HZ
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨z0, rfl⟩ := r.surjective z
    refine ⟨i0 z0, Set.mem_range_self z0, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using
      (congrArg (fun f => f z0) H.w).symm
  · rintro ⟨x0, ⟨z0, rfl⟩, rfl⟩
    refine ⟨r z0, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f z0) H.w

/-- A chart containing the whole special-family image contains the whole
nilpotent deformation.  The constructed factor keeps exactly the same Z. -/
theorem exists_open_factor_of_nilpotentCartesianFamily001
    {B K : Type u} [CommRing B] [CommRing K]
    {X X0 Z Z0 : Scheme.{u}}
    (F : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b)
    (hnil : IsNilpotent (RingHom.ker b))
    (d : X0 ⟶ X) (F0 : X0 ⟶ Spec (.of K))
    (H0 : IsPullback d F0 F (Spec.map (CommRingCat.ofHom b)))
    (i : Z ⟶ X) [IsClosedImmersion i]
    (r : Z0 ⟶ Z) (i0 : Z0 ⟶ X0) (H : IsPullback r i0 i d)
    (U : X.Opens) (hU : ∀ z0, d (i0 z0) ∈ U) :
    ∃ iU : Z ⟶ U, iU ≫ U.ι = i ∧ IsClosedImmersion iU := by
  have hrange : Set.range i ⊆ Set.range U.ι := by
    rw [nilpotentCartesianFamily_range001 F b hb hnil d F0 H0 i r i0 H, U.range_ι]
    rintro _ ⟨_, ⟨z0, rfl⟩, rfl⟩
    exact hU z0
  let iU := IsOpenImmersion.lift U.ι i hrange
  have hfac : iU ≫ U.ι = i := IsOpenImmersion.lift_fac U.ι i hrange
  letI : IsClosedImmersion (iU ≫ U.ι) := hfac.symm ▸ inferInstance
  exact ⟨iU, hfac, IsClosedImmersion.of_comp iU U.ι⟩

section Projective
variable {A : Type u} [CommRing A]
variable {sigma : Type v} [SetLike sigma A] [AddSubgroupClass sigma A]
variable (grading : ℕ → sigma) [GradedRing grading]

/-- Over a local test base the existing all-positive homogeneous chart
construction yields ONE affine chart containing the ENTIRE original
finite-flat family.  No support decomposition or chart-containment premise
is supplied.  The test ring need not be Artinian. -/
theorem finiteFamilyProjective_overLocal_exists_wholeAffineChart001
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (q : X ⟶ Proj grading) (F : X ⟶ Spec (.of R))
    (n : ℕ) (P : FiniteFlatHilbertPoint195 F n) :
    ∃ a : projectivePositiveHomogeneousChartIndex001 grading,
      IsAffineOpen (Proj.basicOpen grading a.val) ∧
      Set.range P.val.subschemeι ⊆ (q ⁻¹ᵁ Proj.basicOpen grading a.val : Set X) := by
  obtain ⟨a, ha⟩ := finiteFamilyProjective_exists_homogeneousWholeChartLocus001
    grading q F n P (closedPoint R)
  have htop : finiteFamilyProjectiveHomogeneousChartLocus001 grading q F n P a = ⊤ :=
    (closedPoint_mem_iff _).mp ha
  refine ⟨a, projectivePositiveHomogeneousChart_isAffine001 grading a, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hz : (P.val.subschemeι ≫ F) z ∈
      finiteFamilyWholeOpenLocus314 F n P (q ⁻¹ᵁ Proj.basicOpen grading a.val) := by
    change (P.val.subschemeι ≫ F) z ∈
      finiteFamilyProjectiveHomogeneousChartLocus001 grading q F n P a
    rw [htop]
    trivial
  exact (mem_finiteFamilyWholeOpenLocus_iff314 F n P
    (q ⁻¹ᵁ Proj.basicOpen grading a.val) _).mp hz z rfl

end Projective
end PfaffianDescent
end
