import PfaffianDescent.NativeNilpotentCoefficientChartLift317
import PfaffianDescent.NativePolynomialChartArtinianCriterion316
import PfaffianDescent.NativeSpecLocalSmoothLocus316
import PfaffianDescent.ProjectivePositiveHomogeneousChartSameRepresenterFinitePresentation
import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterSchemeGlueData
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic

/-!
A physical Artin lifting criterion for smoothness of a locally finitely
presented representing scheme. Affine charts, finite polynomial
presentations, and local Artin obstruction tests are constructed internally.
Lifting physical functor elements across all local Artin square-zero tests
is an explicit hypothesis of the criterion. The later cubic surface
construction supplies this hypothesis for the global Hilbert functor.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

def nativeArtinianAffineTest001 (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

private theorem nativeArtinianSpec_comp001
    (R : Type u) [CommRing R] {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  apply congrArg (fun g : R →+* B => Spec.map (CommRingCat.ofHom g))
  ext r
  exact f.commutes r

private theorem nativeArtinianOpenClassifier_triangle001
    (R : Type u) [CommRing R] {A S : Type u} [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] {X : Scheme.{u}}
    (F : X ⟶ Spec (.of R)) (j : Spec (.of A) ⟶ X)
    (hj : j ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (c : A →ₐ[R] S) :
    (Spec.map (CommRingCat.ofHom c.toRingHom) ≫ j) ≫ F =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  (Category.assoc (Spec.map (CommRingCat.ofHom c.toRingHom)) j F).trans
    ((congrArg (fun k => Spec.map (CommRingCat.ofHom c.toRingHom) ≫ k) hj).trans
      (nativeArtinianSpec_comp001 R c))

def nativeArtinianAffineTestMap001
    (R : Type u) [CommRing R] {B S : Type u} [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] (pi : B →ₐ[R] S) :
    nativeArtinianAffineTest001 R S ⟶ nativeArtinianAffineTest001 R B :=
  Over.homMk (Spec.map (CommRingCat.ofHom pi.toRingHom))
    (nativeArtinianSpec_comp001 R pi)

/-- Explicit arbitrary physical-functor deformation property.  Both test
rings are local Artin R-algebras and the actual quotient kernel squares
to zero.  No chart, classifier, smoothness, or lift outcome is implicit. -/
def PhysicalFunctorArtinianSquareZeroLifts001
    (R : Type u) [CommRing R]
    (P : (Over (Spec (.of R)))ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (B S : Type u) [CommRing B] [CommRing S] [Algebra R B] [Algebra R S]
    [IsLocalRing B] [IsArtinianRing B] [IsLocalRing S] [IsArtinianRing S]
    (pi : B →ₐ[R] S), Function.Surjective pi →
    (RingHom.ker pi.toRingHom) ^ 2 = ⊥ →
    ∀ p : P.obj (.op (nativeArtinianAffineTest001 R S)),
      ∃ q : P.obj (.op (nativeArtinianAffineTest001 R B)),
        P.map (nativeArtinianAffineTestMap001 R pi).op q = p

/-- The same property stated as actual maps into the representing scheme. -/
def NativeRepresenterArtinianSquareZeroLifts001
    (R : Type u) [CommRing R] (H : Over (Spec (.of R))) : Prop :=
  ∀ (B S : Type u) [CommRing B] [CommRing S] [Algebra R B] [Algebra R S]
    [IsLocalRing B] [IsArtinianRing B] [IsLocalRing S] [IsArtinianRing S]
    (pi : B →ₐ[R] S), Function.Surjective pi →
    (RingHom.ker pi.toRingHom) ^ 2 = ⊥ →
    ∀ g : nativeArtinianAffineTest001 R S ⟶ H,
      ∃ d : nativeArtinianAffineTest001 R B ⟶ H,
        nativeArtinianAffineTestMap001 R pi ≫ d = g

/-- Naturality and the actual inverse dictionary transport physical lifts
to classifier lifts.  No separate classifying-map reduction is assumed. -/
theorem nativeRepresenterArtinianLifts_of_physicalFunctorLifts001
    (R : Type u) [CommRing R]
    (P : (Over (Spec (.of R)))ᵒᵖ ⥤ Type u)
    (H : Over (Spec (.of R))) (eta : P ≅ yoneda.obj H)
    (hlift : PhysicalFunctorArtinianSquareZeroLifts001 R P) :
    NativeRepresenterArtinianSquareZeroLifts001 R H := by
  intro B S _ _ _ _ _ _ _ _ pi hpi hsq g
  let a := nativeArtinianAffineTestMap001 R pi
  let p := eta.inv.app (.op (nativeArtinianAffineTest001 R S)) g
  obtain ⟨q, hq⟩ := hlift B S pi hpi hsq p
  refine ⟨eta.hom.app (.op (nativeArtinianAffineTest001 R B)) q, ?_⟩
  have hn := ConcreteCategory.congr_hom (eta.hom.naturality a.op) q
  change eta.hom.app (.op (nativeArtinianAffineTest001 R S)) (P.map a.op q) =
    a ≫ eta.hom.app (.op (nativeArtinianAffineTest001 R B)) q at hn
  exact hn.symm.trans
    ((congrArg (fun p => eta.hom.app (.op (nativeArtinianAffineTest001 R S)) p) hq).trans
      (ConcreteCategory.congr_hom
        (eta.inv_hom_id_app (.op (nativeArtinianAffineTest001 R S))) g))

/-- The actual algebra of ANY affine open chart is smooth from the generic
map-lifting property.  Its finite polynomial presentation and every concrete
Artinian test are derived, rather than supplied as extra hypotheses. -/
theorem nativeOpenAffineProjection_smooth_of_artinianLifts001
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (H : Over (Spec (.of R))) [LocallyOfFinitePresentation H.hom]
    (hlift : NativeRepresenterArtinianSquareZeroLifts001 R H)
    (A : Type u) [CommRing A] [Algebra R A]
    (j : Spec (.of A) ⟶ H.left) [IsOpenImmersion j]
    (hj : j ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  let F := Spec.map (CommRingCat.ofHom (algebraMap R A))
  letI : LocallyOfFinitePresentation F := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    rw [← hj]
    infer_instance
  letI : Algebra.FinitePresentation R A := RingHom.finitePresentation_algebraMap.mp
    ((LocallyOfFinitePresentation.SpecMap_iff
      (CommRingCat.ofHom (algebraMap R A))).mp inferInstance)
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro x _
  letI : x.asIdeal.IsPrime := x.isPrime
  obtain ⟨v, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  have htests : LocalPolynomialArtinianChartLifts316 f hf x.asIdeal := by
    intro N hN
    let LP := Localization.AtPrime (x.asIdeal.comap f.toRingHom)
    let Rel := RingHom.ker (localSurjectivePresentationMap316 f x.asIdeal).toRingHom
    let mx := maximalIdeal LP
    let B := LP ⧸ obstructionThickIdeal316 mx Rel N
    let S := LP ⧸ obstructionThinIdeal316 mx Rel N
    letI : IsNoetherianRing LP := localPolynomial_isNoetherianRing316 R v _
    have hRel : Rel ≤ mx := localPolynomialPresentation_kernel_le_maximal316 f x.asIdeal
    letI : IsLocalRing B := (obstructionThickQuotient_local_artinian316 Rel hRel N hN).1
    letI : IsArtinianRing B := (obstructionThickQuotient_local_artinian316 Rel hRel N hN).2
    letI : IsLocalRing S := (obstructionThinQuotient_local_artinian316 Rel hRel N hN).1
    letI : IsArtinianRing S := (obstructionThinQuotient_local_artinian316 Rel hRel N hN).2
    let pi : B →ₐ[R] S := Ideal.Quotient.factorₐ R
      (obstructionThickIdeal_le_thin316 mx Rel N)
    have hpi : Function.Surjective pi := Ideal.Quotient.factor_surjective
      (obstructionThickIdeal_le_thin316 mx Rel N)
    have hsq : (RingHom.ker pi.toRingHom) ^ 2 = ⊥ :=
      obstructionQuotientReduction_kernel_sq_zero316 mx Rel N hRel
    let c : A →ₐ[R] S := localPolynomialArtinianChartTest316 f hf x.asIdeal N
    let g : nativeArtinianAffineTest001 R S ⟶ H :=
      Over.homMk (Spec.map (CommRingCat.ofHom c.toRingHom) ≫ j) (by
        exact nativeArtinianOpenClassifier_triangle001 R H.hom j hj c)
    obtain ⟨d, hd⟩ := hlift B S pi hpi hsq g
    have hred : Spec.map (CommRingCat.ofHom pi.toRingHom) ≫ d.left =
        Spec.map (CommRingCat.ofHom c.toRingHom) ≫ j :=
      congrArg (fun a : nativeArtinianAffineTest001 R S ⟶ H => a.left) hd
    obtain ⟨l, hl, _⟩ := nativeAlgebraLift_of_nilpotentOpenDiagram317 R H.hom j hj
      pi hpi (show IsNilpotent (RingHom.ker pi.toRingHom) from ⟨2, hsq⟩)
      c d.left d.w hred
    exact ⟨l, hl⟩
  exact nativeSpec_mem_smoothLocus_of_localization316 R A x
    (formallySmooth_atPrime_of_polynomial_chart_lifts316 f hf x.asIdeal htests)

/-- Generic scheme-level criterion.  The source affine cover, its scalar
algebras, and every polynomial presentation used by316 are derived here. -/
theorem nativeRepresenter_smooth_of_artinianLifts001
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (H : Over (Spec (.of R))) [LocallyOfFinitePresentation H.hom]
    (hlift : NativeRepresenterArtinianSquareZeroLifts001 R H) : Smooth H.hom := by
  letI : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{u}) (Q := RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth.{u}) H.left.affineCover
  intro i
  let Y := H.left.affineCover.X i
  let A := Γ(Y, ⊤)
  let j : Spec (.of A) ⟶ H.left := Y.isoSpec.inv ≫ H.left.affineCover.f i
  let f : R →+* A := (Spec.preimage (j ≫ H.hom)).hom
  letI : Algebra R A := f.toAlgebra
  have hj : j ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
    (Spec.map_preimage (j ≫ H.hom)).symm
  letI : IsOpenImmersion j := inferInstance
  have hs := nativeOpenAffineProjection_smooth_of_artinianLifts001 R H hlift A j hj
  letI : Smooth (j ≫ H.hom) := hj.symm ▸ hs
  have heq : H.left.affineCover.f i ≫ H.hom = Y.isoSpec.hom ≫ (j ≫ H.hom) := by
    simp only [j, Category.assoc, Iso.hom_inv_id_assoc]
  rw [heq]
  infer_instance

/-- Apply the generic criterion directly to any actual physical functor
and its SAME representing NatIso.  For the projective chart application,
P is relativeFiniteFlatHilbertFunctor197 and eta is the accepted all-test
representing iso; no normalized cubic coordinate chart is involved. -/
theorem representedPhysicalFunctor_smooth_of_artinianLifts001
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (P : (Over (Spec (.of R)))ᵒᵖ ⥤ Type u)
    (H : Over (Spec (.of R))) [LocallyOfFinitePresentation H.hom]
    (eta : P ≅ yoneda.obj H)
    (hlift : PhysicalFunctorArtinianSquareZeroLifts001 R P) : Smooth H.hom :=
  nativeRepresenter_smooth_of_artinianLifts001 R H
    (nativeRepresenterArtinianLifts_of_physicalFunctorLifts001 R P H eta hlift)

/-- Exact all-positive chart application.  Both the SAME chosen classifier
and its LFP are the accepted internally constructed ones.  The only new
deformation obligation is the explicit physical square-zero Artin lifting
property for arbitrary families in this chart; no normalized coordinates,
polynomial presentation, chart smoothness or global smoothness is assumed. -/
theorem originalPositiveHomogeneousChartIndex_smooth_of_physicalArtinianLifts001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma R))
    (n : ℕ) (hn : 0 < n)
    (a : projectivePositiveHomogeneousChartIndex001
      (AllCharacteristics.HomogeneousProjective.grading I))
    (hlift : PhysicalFunctorArtinianSquareZeroLifts001 R
      (relativeFiniteFlatHilbertFunctor197
        ((Proj.basicOpen (AllCharacteristics.HomogeneousProjective.grading I) a.val).ι ≫
          AllCharacteristics.HomogeneousProjective.toBase I) n)) :
    Smooth (originalPositiveHomogeneousChartIndexRepresentingObject001 I n hn a).hom := by
  let H := originalPositiveHomogeneousChartIndexRepresentingObject001 I n hn a
  let eta := originalPositiveHomogeneousChartIndexRepresentingIso001 I n hn a
  letI : LocallyOfFinitePresentation H.hom :=
    originalPositiveHomogeneousChart_sameAllTestHilbertRepresenter_locallyOfFinitePresentation001
      I a.val (Classical.choose a.property) (Classical.choose_spec a.property).1
      (Classical.choose_spec a.property).2 n hn H eta
  exact representedPhysicalFunctor_smooth_of_artinianLifts001 R _ H eta hlift

end PfaffianDescent
end
