import PfaffianDescent.WholeFamilyAffineTensorQuotient
import PfaffianDescent.CubicAffineTensorResidueSupport
import PfaffianDescent.OriginalArtinPrincipalHilbertBurch318
import PfaffianDescent.PrincipalAffineReductionChart
import PfaffianDescent.WholeAffineQuotientPrincipalShrinking
import PfaffianDescent.GenericAffineHilbertBurchPhysicalLift
import PfaffianDescent.HilbertBurchRowLocalization318

/-!
Physical lifting for an arbitrary original finite-flat Hilbert point on a
cubic surface. The construction produces its whole affine quotient, the
residual surface data, semilocal and principal Hilbert--Burch matrices,
and an upstairs finite-flat family whose whole ideal reduces to the
original embedded ideal.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix Module
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.HilbertSurfaceDraft
open scoped TensorProduct BigOperators
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

private theorem cofactor_allRelations_of_exact001
    {A : Type u} [CommRing A] {m : ℕ}
    (M : Matrix (Option (Fin m)) (Fin m) A)
    (hex : Function.Exact M.mulVecLin (rowFunctional008 (hilbertBurchCofactors318 M))) :
    ∀ v : Option (Fin m) → A,
      (∑ i, v i * hilbertBurchCofactors318 M i) = 0 →
      ∃ w : Fin m → A, ∀ i, v i = ∑ j, M i j * w j := by
  intro v hv
  have hk : v ∈ LinearMap.ker (rowFunctional008 (hilbertBurchCofactors318 M)) := by
    change (∑ i, hilbertBurchCofactors318 M i * v i) = 0
    simpa only [mul_comm] using hv
  rw [hex.linearMap_ker_eq] at hk
  obtain ⟨w, hw⟩ := hk
  exact ⟨w, fun i ↦ (congrFun hw i).symm⟩

/-- No downstairs ideal presentation or upstairs lift certificate occurs
in this theorem's inputs.  The nonzero residue equation is the ordinary
surface condition, derived separately from the original primitive cubic. -/
theorem exists_arbitraryCubicArtinFamily_physicalLift001
    {B S C : Type u} [CommRing B] [CommRing S] [IsLocalRing S]
    [IsArtinianRing S] [Algebra B S] [CommRing C]
    {sigma : Type v} [SetLike sigma C] [AddSubgroupClass sigma C]
    (grading : ℕ → sigma) [GradedRing grading]
    {X : Scheme.{u}} (qproj : X ⟶ Proj grading) [IsAffineHom qproj]
    (F : X ⟶ Spec (.of B)) [hSmooth : Smooth F] [hSeparated : IsSeparated F]
    (q : MvPolynomial (Fin 4) S) (hq : q.IsHomogeneous 3)
    (hres : q.map (algebraMap S (IsLocalRing.ResidueField S)) ≠ 0)
    (d : hypersurface q hq ⟶ X)
    (Hbase : IsPullback d (hypersurfaceToBase q hq) F
      (Spec.map (CommRingCat.ofHom (algebraMap B S))))
    (hBS : Function.Surjective (algebraMap B S))
    (hI : (RingHom.ker (algebraMap B S)) ^ 2 = ⊥)
    (n : ℕ) (P : FiniteFlatHilbertPoint195 (hypersurfaceToBase q hq) n) :
    ∃ Q : FiniteFlatHilbertPoint195 F n,
      finiteFlatHilbertBaseChange195 d (hypersurfaceToBase q hq) F
        (Spec.map (CommRingCat.ofHom (algebraMap B S))) Hbase n Q = P := by
  let F0 := hypersurfaceToBase q hq
  letI : Smooth F0 := MorphismProperty.of_isPullback Hbase (inferInstance : Smooth F)
  obtain ⟨T, J, hfinite, hflat, hn, hP⟩ :=
    exists_wholeFamilyAffineTensorQuotient001 grading qproj F F0 d Hbase n P
  let A := S ⊗[B] T.A
  letI : Module.Finite S (A ⧸ J) := hfinite
  letI : Module.Flat S (A ⧸ J) := hflat
  letI : IsArtinianRing (A ⧸ J) := IsArtinianRing.of_finite S (A ⧸ J)
  letI : IsOpenImmersion T.a0 := MorphismProperty.of_isPullback T.cartesian
    (inferInstance : IsOpenImmersion T.a)
  letI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap S A))) := by
    rw [← T.specialToBase]
    infer_instance
  letI : Module.Flat S A := RingHom.flat_algebraMap_iff.mp
    (Flat.SpecMap_iff.mp (inferInstance : Flat
      (Spec.map (CommRingCat.ofHom (algebraMap S A)))))
  letI : Algebra.FinitePresentation S A := RingHom.finitePresentation_algebraMap.mp
    ((LocallyOfFinitePresentation.SpecMap_iff
      (CommRingCat.ofHom (algebraMap S A))).mp inferInstance)
  let k := IsLocalRing.ResidueField S
  let p := q.map (algebraMap S k)
  let hp := hq.map (algebraMap S k)
  obtain ⟨hArt, hgeom⟩ := exists_cubicAffineTensorResidueSupport_localSurface001
    (S := S) (K := k) (A := A)
    (by
      change Function.Surjective (algebraMap S (IsLocalRing.ResidueField S))
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      exact IsLocalRing.residue_surjective) q hq p hp hres rfl
    T.a0 T.specialToBase J
  letI := hArt
  obtain ⟨m, r, N, hr, hN⟩ :=
    exists_originalArtinSupport_principal_hilbertBurch318 S A J
      (fun x hx ↦ (hgeom x hx).1) (fun x hx ↦ (hgeom x hx).2)
  obtain ⟨hJr, hexr⟩ := hN r dvd_rfl
  let π := affineTensorFiberReduction174 (R := B) (S := S) (A := T.A)
  have hπ : Function.Surjective π := affineTensorFiberReduction174_surjective hBS
  obtain ⟨r', hr'⟩ := hπ r
  let πr := actualAwayAlgHom022 π r' r hr'
  let ar := Spec.map (CommRingCat.ofHom (algebraMap T.A (Localization.Away r'))) ≫ T.a
  let a0r := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))) ≫ T.a0
  obtain ⟨hopen, har, Hchart, hπr, hkerπr⟩ := principalAffineReductionChart001
    F d T.a T.toBase π hπ (RingHom.ker (algebraMap B S))
    (affineTensorFiberReduction174_kernel (A := T.A) hBS) T.a0 T.cartesian r' r hr'
  letI : IsOpenImmersion ar := hopen
  let Jr := J.map (algebraMap A (Localization.Away r))
  obtain ⟨hfiniter, hflatr, hrankr, hwhole⟩ :=
    wholeAffineQuotient_principalShrink_properties001 (S := S) (A := A) J r hr T.a0
  letI : Module.Finite S (Localization.Away r ⧸ Jr) := hfiniter
  letI : Module.Flat S (Localization.Away r ⧸ Jr) := hflatr
  obtain ⟨Q, hQ⟩ := exists_genericAffineHilbertBurch_globalPhysicalLift001
    F F0 d Hbase ar har πr hπr hkerπr a0r Hchart hBS hI
    (N.map (algebraMap A (Localization.Away r))) Jr hJr
    (cofactor_allRelations_of_exact001 _ hexr) n (hrankr.trans hn)
  exact ⟨Q, Subtype.ext (hQ.trans (hwhole.trans hP.symm))⟩

end PfaffianDescent
end
