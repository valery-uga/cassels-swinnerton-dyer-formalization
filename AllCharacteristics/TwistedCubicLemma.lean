import PfaffianDescent.QuarticTwistedCubicSmooth
import AllCharacteristics.HomogeneousProjectiveAmbient
import AllCharacteristics.ProjectiveBaseChange
import AllCharacteristics.SmoothSchemeRegularity

/-!
# Embedded geometrically standard twisted cubics

This gives the homogeneous-Proj model of the embedded curve in
`lem:twisted-cubic` of `2-proofs.tex`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
open HomogeneousProjective PfaffianDescent

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u

/-- A closed immersion is canonically the subscheme associated to its kernel
ideal sheaf.  This is the first scheme-theoretic step in converting an
arbitrary embedded curve into homogeneous equations. -/
theorem closedImmersion_iso_kernelSubscheme
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] :
    ∃ e : X ≅ i.ker.subscheme, e.hom ≫ i.ker.subschemeι = i := by
  refine ⟨asIso i.toImage, ?_⟩
  exact i.toImage_imageι

/-- The kernel ideal sheaf of a closed immersion with reduced source is
radical.  On every affine target open, the induced map on sections is
surjective and has a reduced quotient. -/
theorem closedImmersion_ker_radical_of_reduced_source
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] [IsReduced X] :
    i.ker.radical = i.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.radical_ideal, i.ker_apply U]
  apply Ideal.radical_eq_iff.mpr
  rw [RingHom.ker_isRadical_iff_reduced_of_surjective
    (i.app_surjective U U.2)]
  infer_instance

/-- A reduced closed immersion is the reduced induced closed subscheme on
its support. -/
theorem closedImmersion_ker_eq_vanishingIdeal_support_of_reduced_source
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] [IsReduced X] :
    i.ker = Scheme.IdealSheafData.vanishingIdeal i.ker.support := by
  exact (Scheme.IdealSheafData.vanishingIdeal_support.trans
    (closedImmersion_ker_radical_of_reduced_source i)).symm

/-- For a reduced closed subscheme of projective space, the support of the
kernel ideal sheaf agrees with that of the homogeneous vanishing ideal of its
image. -/
theorem supports_eq_closedImmersionVanishingIdeal
    {R : Type u} {σ : Type} [CommRing R]
    {X : Scheme.{u}} (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion i] [IsReduced X] :
    i.ker.support =
      (quotientProjMap (closedImmersionVanishingIdeal i)).ker.support := by
  let J := closedImmersionVanishingIdeal i
  let j := quotientProjMap J
  letI : IsClosedImmersion j := quotientProjMap_isClosedImmersion J
  have hjrange : Set.range j = Set.range i := by
    exact (range_quotientProjMap J).trans
      (zeroLocus_closedImmersionVanishingIdeal i)
  ext x
  rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker]
  rw [i.isClosedEmbedding.isClosed_range.closure_eq,
    j.isClosedEmbedding.isClosed_range.closure_eq, hjrange]

/-- A reduced closed projective subscheme is the canonical Proj subscheme of
the homogeneous vanishing ideal of its image. -/
theorem kernels_eq_closedImmersionVanishingIdeal
    {R : Type u} {σ : Type} [CommRing R]
    {X : Scheme.{u}} (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion i] [IsReduced X] :
    i.ker = (quotientProjMap (closedImmersionVanishingIdeal i)).ker := by
  let J := closedImmersionVanishingIdeal i
  let j := quotientProjMap J
  letI : IsClosedImmersion j := quotientProjMap_isClosedImmersion J
  letI : IsReduced (scheme J) := scheme_closedImmersionVanishingIdeal_isReduced i
  have hsupport : i.ker.support = j.ker.support :=
    supports_eq_closedImmersionVanishingIdeal i
  calc
    i.ker = Scheme.IdealSheafData.vanishingIdeal i.ker.support :=
      closedImmersion_ker_eq_vanishingIdeal_support_of_reduced_source i
    _ = Scheme.IdealSheafData.vanishingIdeal j.ker.support := by rw [hsupport]
    _ = j.ker :=
      (closedImmersion_ker_eq_vanishingIdeal_support_of_reduced_source j).symm

/-- The map from a reduced closed projective subscheme to the Proj of its
homogeneous vanishing ideal. -/
noncomputable def closedImmersionHomogeneousRecoveryMap
    {R : Type u} {σ : Type} [CommRing R]
    {X : Scheme.{u}} (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion i] [IsReduced X] :
    X ⟶ scheme (closedImmersionVanishingIdeal i) := by
  let J := closedImmersionVanishingIdeal i
  let j := quotientProjMap J
  letI : IsClosedImmersion j := quotientProjMap_isClosedImmersion J
  exact IsClosedImmersion.lift j i
    (kernels_eq_closedImmersionVanishingIdeal i).symm.le

theorem closedImmersionHomogeneousRecoveryMap_fac
    {R : Type u} {σ : Type} [CommRing R]
    {X : Scheme.{u}} (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion i] [IsReduced X] :
    closedImmersionHomogeneousRecoveryMap i ≫
      quotientProjMap (closedImmersionVanishingIdeal i) = i := by
  exact IsClosedImmersion.lift_fac _ _ _

/-- The scheme-theoretic reconstruction of a reduced closed projective
subscheme from the homogeneous vanishing ideal of its image. -/
noncomputable def closedImmersionHomogeneousRecoveryIso
    {R : Type u} {σ : Type} [CommRing R]
    {X : Scheme.{u}} (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion i] [IsReduced X] :
    X ≅ scheme (closedImmersionVanishingIdeal i) := by
  let J := closedImmersionVanishingIdeal i
  let j := quotientProjMap J
  letI : IsClosedImmersion j := quotientProjMap_isClosedImmersion J
  letI : IsIso (closedImmersionHomogeneousRecoveryMap i) :=
    IsClosedImmersion.isIso_of_ker_eq i j
      (closedImmersionHomogeneousRecoveryMap i)
      (closedImmersionHomogeneousRecoveryMap_fac i)
      (kernels_eq_closedImmersionVanishingIdeal i)
  exact asIso (closedImmersionHomogeneousRecoveryMap i)

theorem closedImmersionHomogeneousRecoveryIso_hom_fac
    {R : Type u} {σ : Type} [CommRing R]
    {X : Scheme.{u}} (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion i] [IsReduced X] :
    (closedImmersionHomogeneousRecoveryIso i).hom ≫
      quotientProjMap (closedImmersionVanishingIdeal i) = i := by
  exact closedImmersionHomogeneousRecoveryMap_fac i


/-- The recovered homogeneous presentation is over the same coefficient
spectrum as the original embedded curve. -/
theorem closedImmersionHomogeneousRecoveryIso_hom_toBase
    {R : Type u} {σ : Type} [CommRing R]
    {X : Scheme.{u}} (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion i] [IsReduced X] :
    (closedImmersionHomogeneousRecoveryIso i).hom ≫
      toBase (closedImmersionVanishingIdeal i) = i ≫ ambientToBase := by
  rw [← quotientProjMap_toBase]
  rw [← Category.assoc, closedImmersionHomogeneousRecoveryIso_hom_fac]

/-- Coefficient extension of the canonical homogeneous ideal is the actual
categorical base change of a reduced closed projective subscheme.  This makes
the algebraic-closure condition in `lem:twisted-cubic` a condition on the
paper's genuine base-changed curve, rather than on an auxiliary Proj model. -/
noncomputable def closedImmersionHomogeneousRecoveryBaseChangeIso
    {R S : Type u} {σ : Type} [CommRing R] [CommRing S]
    (f : R →+* S)
    {X : Scheme.{u}} (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion i] [IsReduced X] :
    scheme (HomogeneousIdeal.map (ambientCoefficientGradedRingHom f)
      (closedImmersionVanishingIdeal i)) ≅
      pullback (i ≫ ambientToBase) (Spec.map (CommRingCat.ofHom f)) := by
  let I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R) :=
    closedImmersionVanishingIdeal i
  let J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ S) :=
    HomogeneousIdeal.map (ambientCoefficientGradedRingHom f) I
  have hIJ : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal := by
    change I.toIdeal.map (ambientCoefficientGradedRingHom f) =
      (HomogeneousIdeal.map (ambientCoefficientGradedRingHom f) I).toIdeal
    exact (HomogeneousIdeal.toIdeal_map _).symm
  let e : scheme J ≅ pullback (toBase I) (Spec.map (CommRingCat.ofHom f)) :=
    projectiveBaseChangeIso f I J hIJ
  let r : X ≅ scheme I := closedImmersionHomogeneousRecoveryIso i
  let q : pullback (toBase I) (Spec.map (CommRingCat.ofHom f)) ⟶
      pullback (i ≫ ambientToBase) (Spec.map (CommRingCat.ofHom f)) :=
    pullback.map (toBase I) (Spec.map (CommRingCat.ofHom f))
      (i ≫ ambientToBase) (Spec.map (CommRingCat.ofHom f)) r.inv (𝟙 _) (𝟙 _) (by
        rw [Category.comp_id, ← closedImmersionHomogeneousRecoveryIso_hom_toBase i,
          ← Category.assoc, Iso.inv_hom_id, Category.id_comp]) (by simp)
  letI : IsIso q := pullback.map_isIso (toBase I) (Spec.map (CommRingCat.ofHom f))
    (i ≫ ambientToBase) (Spec.map (CommRingCat.ofHom f)) r.inv (𝟙 _) (𝟙 _) (by
      rw [Category.comp_id, ← closedImmersionHomogeneousRecoveryIso_hom_toBase i,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp]) (by simp)
  exact e ≪≫ asIso q

/-- The base-change identification respects the original ambient projective
embedding after applying the coefficient morphism. -/
theorem closedImmersionHomogeneousRecoveryBaseChangeIso_hom_ambient
    {R S : Type u} {σ : Type} [CommRing R] [CommRing S]
    (f : R →+* S)
    {X : Scheme.{u}} (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion i] [IsReduced X] :
    (closedImmersionHomogeneousRecoveryBaseChangeIso f i).hom ≫
      pullback.fst (i ≫ ambientToBase) (Spec.map (CommRingCat.ofHom f)) ≫ i =
      quotientProjMap (HomogeneousIdeal.map (ambientCoefficientGradedRingHom f)
        (closedImmersionVanishingIdeal i)) ≫ ambientCoefficientMap f := by
  unfold closedImmersionHomogeneousRecoveryBaseChangeIso
  dsimp only
  rw [Iso.trans_hom, Category.assoc]
  simp only [asIso_hom]
  unfold pullback.map
  simp only [Category.assoc, pullback.lift_fst_assoc]
  have hr : (closedImmersionHomogeneousRecoveryIso i).inv ≫ i =
      quotientProjMap (closedImmersionVanishingIdeal i) := by
    calc
      (closedImmersionHomogeneousRecoveryIso i).inv ≫ i =
          (closedImmersionHomogeneousRecoveryIso i).inv ≫
            ((closedImmersionHomogeneousRecoveryIso i).hom ≫
              quotientProjMap (closedImmersionVanishingIdeal i)) :=
        congrArg (fun h => (closedImmersionHomogeneousRecoveryIso i).inv ≫ h)
          (closedImmersionHomogeneousRecoveryIso_hom_fac i).symm
      _ = quotientProjMap (closedImmersionVanishingIdeal i) := by simp
  rw [hr, ← Category.assoc, projectiveBaseChangeIso_hom_fst]
  exact projectiveCoefficientMap_comp_quotientProjMap _ _ _ _

/-- The scheme-theoretic assertion that an embedded curve becomes a twisted
cubic after changing coefficients.  By
`closedImmersionHomogeneousRecoveryBaseChangeIso`, this condition is imposed
on the actual categorical base change of the curve and its ambient embedding. -/
def IsTwistedCubicAfterCoefficientExtension
    {R S : Type u} [Field R] [Field S] (f : R →+* S)
    {X : Scheme.{u}} (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) R))
    [IsClosedImmersion i] : Prop :=
  QuarticNet.GroundTwistedCubicPresentation
    (HomogeneousIdeal.map (ambientCoefficientGradedRingHom f)
      (closedImmersionVanishingIdeal i))

private theorem standardTwistedCubic_not_irrelevant_le
    {k : Type u} [Field k] :
    ¬ HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 4) k) ≤
      QuarticNet.standardTwistedCubicHomogeneousIdeal (K := k) := by
  intro h
  have hx : MvPolynomial.X (R := k) 0 ∈
      QuarticNet.standardTwistedCubicHomogeneousIdeal (K := k) :=
    h (by
      apply HomogeneousIdeal.mem_irrelevant_of_mem
        (MvPolynomial.homogeneousSubmodule (Fin 4) k) (i := 1) (by norm_num)
      exact MvPolynomial.isHomogeneous_X k 0)
  change MvPolynomial.X (R := k) 0 ∈ QuarticNet.standardTwistedCubicIdeal k at hx
  rw [QuarticNet.standardTwistedCubicIdeal_eq_ker] at hx
  have hne : QuarticNet.standardTwistedCubicParam k (MvPolynomial.X 0) ≠ 0 := by
    simp only [QuarticNet.standardTwistedCubicParam, MvPolynomial.aeval_X,
      Matrix.cons_val_zero]
    exact pow_ne_zero _ (MvPolynomial.X_ne_zero (R := k) 0)
  exact hne hx

/-- The homogeneous ideal of the standard embedded twisted cubic is recovered
from the projective image of its canonical closed immersion. -/
theorem standardTwistedCubic_closedImmersionVanishingIdeal
    {k : Type u} [Field k] :
    closedImmersionVanishingIdeal
      (quotientProjMap (QuarticNet.standardTwistedCubicHomogeneousIdeal (K := k))) =
        QuarticNet.standardTwistedCubicHomogeneousIdeal (K := k) := by
  exact closedImmersionVanishingIdeal_eq_of_iso_quotient
    (QuarticNet.standardTwistedCubicHomogeneousIdeal (K := k))
    (by
      change (QuarticNet.standardTwistedCubicIdeal k).IsPrime
      exact QuarticNet.standardTwistedCubicIdeal_isPrime k)
    standardTwistedCubic_not_irrelevant_le
    (quotientProjMap (QuarticNet.standardTwistedCubicHomogeneousIdeal (K := k)))
    (Iso.refl _)
    (by simp)

/-- A ground-coordinate twisted-cubic presentation has a prime defining
ideal, because an invertible linear coordinate change identifies it with the
prime standard ideal. -/
theorem groundTwistedCubicPresentation_isPrime
    {k : Type u} [Field k]
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k)}
    (hI : QuarticNet.GroundTwistedCubicPresentation I) : I.toIdeal.IsPrime := by
  obtain ⟨M, hM⟩ := hI
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) k).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  let E := linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) k) hdet
  have hEM : I.toIdeal.map E.toRingHom = QuarticNet.standardTwistedCubicIdeal k := by
    change I.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) k) hdet).toRingHom = _
    have hE :
        (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) k) hdet).toRingEquiv.toRingHom =
          (linearSubstitution (M : Matrix (Fin 4) (Fin 4) k)).toRingHom := rfl
    rw [hE]
    exact hM
  rw [← Ideal.map_of_equiv E.toRingEquiv (I := I.toIdeal)]
  change (I.toIdeal.map
      (↑E.toRingEquiv : MvPolynomial (Fin 4) k →+* MvPolynomial (Fin 4) k)).map
        (↑E.toRingEquiv.symm : MvPolynomial (Fin 4) k →+* MvPolynomial (Fin 4) k) |>.IsPrime
  change I.toIdeal.map
      (↑E.toRingEquiv : MvPolynomial (Fin 4) k →+* MvPolynomial (Fin 4) k) =
        QuarticNet.standardTwistedCubicIdeal k at hEM
  rw [hEM]
  letI : (QuarticNet.standardTwistedCubicIdeal k).IsPrime :=
    QuarticNet.standardTwistedCubicIdeal_isPrime k
  exact Ideal.map_isPrime_of_equiv E.toRingEquiv.symm

/-- A ground-coordinate twisted-cubic presentation is relevant: its defining
ideal does not contain the irrelevant ideal of projective three-space. -/
theorem groundTwistedCubicPresentation_not_irrelevant_le
    {k : Type u} [Field k]
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k)}
    (hI : QuarticNet.GroundTwistedCubicPresentation I) :
    ¬ HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 4) k) ≤ I := by
  obtain ⟨M, hM⟩ := hI
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) k).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  let E := linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) k) hdet
  have hEM : I.toIdeal.map E.toRingHom = QuarticNet.standardTwistedCubicIdeal k := by
    change I.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) k) hdet).toRingHom = _
    have hE :
        (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) k) hdet).toRingEquiv.toRingHom =
          (linearSubstitution (M : Matrix (Fin 4) (Fin 4) k)).toRingHom := rfl
    rw [hE]
    exact hM
  intro h
  apply standardTwistedCubic_not_irrelevant_le (k := k)
  apply (HomogeneousIdeal.irrelevant_le
    (MvPolynomial.homogeneousSubmodule (Fin 4) k)).mpr
  intro n hn f hf
  change f ∈ QuarticNet.standardTwistedCubicIdeal k
  rw [← hEM]
  change f ∈ I.toIdeal.map (↑E.toRingEquiv :
    MvPolynomial (Fin 4) k →+* MvPolynomial (Fin 4) k)
  apply (Ideal.mem_map_of_equiv E.toRingEquiv f).mpr
  refine ⟨linearSubstitution (M : Matrix (Fin 4) (Fin 4) k)⁻¹ f, ?_, ?_⟩
  · apply h
    apply HomogeneousIdeal.mem_irrelevant_of_mem
      (MvPolynomial.homogeneousSubmodule (Fin 4) k) (i := n) hn
    exact linearSubstitution_homogeneous
      ((M : Matrix (Fin 4) (Fin 4) k)⁻¹) hf
  · change linearSubstitution (M : Matrix (Fin 4) (Fin 4) k)
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) k)⁻¹ f) = f
    rw [← AlgHom.comp_apply, linearSubstitution_comp,
      Matrix.nonsing_inv_mul (M : Matrix (Fin 4) (Fin 4) k) hdet,
      linearSubstitution_one]
    rfl

/-- A ground-coordinate twisted-cubic presentation becomes a geometrically
standard presentation after extending scalars to the algebraic closure. -/
theorem groundTwistedCubicPresentation_geometricallyStandard
    {k : Type u} [Field k]
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k)}
    (hI : QuarticNet.GroundTwistedCubicPresentation I) :
    QuarticNet.GeometricallyStandardTwistedCubic I := by
  obtain ⟨M, hM⟩ := hI
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap k (AlgebraicClosure k)) M, ?_⟩
  change (I.toIdeal.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))).map
      (linearSubstitution
        ((M : Matrix (Fin 4) (Fin 4) k).map (algebraMap k (AlgebraicClosure k)))).toRingHom =
      QuarticNet.standardTwistedCubicIdeal (AlgebraicClosure k)
  rw [← ideal_map_linearSubstitution_map (algebraMap k (AlgebraicClosure k))
    I.toIdeal (M : Matrix (Fin 4) (Fin 4) k), hM]
  exact QuarticNet.standardTwistedCubicIdeal_map_coefficientExtension

/-- If the coefficient extension of a homogeneous ideal to the algebraic
closure is a ground-coordinate standard twisted cubic, then the original
ideal satisfies the geometric-coordinate hypothesis used in the descent
theorem.  This is the ideal-level reading of the paper's phrase that the
embedded curve becomes a twisted cubic over the algebraic closure. -/
theorem geometricallyStandardTwistedCubic_of_algebraicClosure_groundPresentation
    {k : Type u} [Field k]
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k)}
    (hbar : QuarticNet.GroundTwistedCubicPresentation
      (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom (algebraMap k (AlgebraicClosure k))) I)) :
    QuarticNet.GeometricallyStandardTwistedCubic I := by
  rcases hbar with ⟨M, hM⟩
  exact ⟨M, hM⟩


/-- The geometric-coordinate condition is equivalently a ground-coordinate
standard presentation of the coefficient extension of the ideal.  Thus the
algebraic-closure hypothesis of `lem:twisted-cubic` is represented without a
choice of equations for the original curve. -/
theorem algebraicClosure_groundPresentation_of_geometricallyStandardTwistedCubic
    {k : Type u} [Field k]
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k)}
    (hgeo : QuarticNet.GeometricallyStandardTwistedCubic I) :
    QuarticNet.GroundTwistedCubicPresentation
      (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom (algebraMap k (AlgebraicClosure k))) I) := by
  rcases hgeo with ⟨M, hM⟩
  exact ⟨M, hM⟩

/-- The two homogeneous-coordinate formulations of an embedded curve becoming
a twisted cubic over the algebraic closure are equivalent. -/
theorem algebraicClosure_groundPresentation_iff_geometricallyStandardTwistedCubic
    {k : Type u} [Field k]
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k)} :
    QuarticNet.GroundTwistedCubicPresentation
      (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom (algebraMap k (AlgebraicClosure k))) I) ↔
      QuarticNet.GeometricallyStandardTwistedCubic I :=
  ⟨geometricallyStandardTwistedCubic_of_algebraicClosure_groundPresentation,
    algebraicClosure_groundPresentation_of_geometricallyStandardTwistedCubic⟩

/-- An ambient-compatible Proj presentation by a ground-coordinate twisted
cubic identifies the canonical vanishing ideal of the actual embedded curve. -/
theorem closedImmersionVanishingIdeal_eq_of_groundTwistedCubicPresentation
    {k : Type u} [Field k]
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k)}
    (hI : QuarticNet.GroundTwistedCubicPresentation I)
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (e : X ≅ scheme I)
    (he : e.hom ≫ quotientProjMap I = i) :
    closedImmersionVanishingIdeal i = I :=
  closedImmersionVanishingIdeal_eq_of_iso_quotient I
    (groundTwistedCubicPresentation_isPrime hI)
    (groundTwistedCubicPresentation_not_irrelevant_le hI) i e he

/-- A closed projective Proj subscheme in `P³` whose algebraic-closure
embedding is a standard twisted cubic.  The ambient morphism is the canonical
closed immersion of the homogeneous Proj model. -/
structure EmbeddedGeometricallyStandardTwistedCubic (k : Type u) [Field k] where
  ideal : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k)
  geometricallyStandard : QuarticNet.GeometricallyStandardTwistedCubic ideal

namespace EmbeddedGeometricallyStandardTwistedCubic

variable {k : Type u} [Field k]

/-- The projective curve represented by the homogeneous ideal. -/
noncomputable abbrev curve (C : EmbeddedGeometricallyStandardTwistedCubic k) : Scheme.{u} :=
  scheme C.ideal

/-- The closed immersion of the curve into the projective three-space. -/
noncomputable abbrev embedding (C : EmbeddedGeometricallyStandardTwistedCubic k) :
    C.curve ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k) :=
  quotientProjMap C.ideal

instance embedding_isClosedImmersion (C : EmbeddedGeometricallyStandardTwistedCubic k) :
    IsClosedImmersion C.embedding := by
  change IsClosedImmersion (quotientProjMap C.ideal)
  infer_instance

/-- The ground-field coordinate meaning of the conclusion that the ambient
embedding is a twisted cubic. -/
def IsTwistedCubic (C : EmbeddedGeometricallyStandardTwistedCubic k) : Prop :=
  QuarticNet.GroundTwistedCubicPresentation C.ideal

/-- The homogeneous-Proj form of `lem:twisted-cubic` over a perfect field. -/
theorem descent_perfect (C : EmbeddedGeometricallyStandardTwistedCubic k) [PerfectField k] :
    QuarticNet.GroundTwistedCubicPresentation C.ideal ∧
      ∃ e : C.curve ≅ projectiveLineProj k,
        e.hom ≫ projectiveLineProjToBase k = toBase C.ideal ∧
          Smooth (toBase C.ideal) ∧
            ∃ s : Spec (.of k) ⟶ C.curve, s ≫ toBase C.ideal = 𝟙 _ := by
  let hground : QuarticNet.GroundTwistedCubicPresentation C.ideal :=
    QuarticNet.groundTwistedCubicPresentation_of_geometricallyStandardTwistedCubic
      C.geometricallyStandard
  obtain ⟨e, he, hsmooth, s, hs⟩ :=
    QuarticNet.twistedCubic_descent_perfect_overBase C.geometricallyStandard
  exact ⟨hground, e, he, hsmooth, s, hs⟩

/-- The arbitrary-field descent statement when the geometric coordinate
standardization is already defined over the separable closure. -/
theorem descent_separable (C : EmbeddedGeometricallyStandardTwistedCubic k)
    (hgeo : QuarticNet.SeparableGeometricallyStandardTwistedCubic C.ideal) :
    QuarticNet.GroundTwistedCubicPresentation C.ideal ∧
      ∃ e : C.curve ≅ projectiveLineProj k,
        e.hom ≫ projectiveLineProjToBase k = toBase C.ideal ∧
          Smooth (toBase C.ideal) ∧
            ∃ s : Spec (.of k) ⟶ C.curve, s ≫ toBase C.ideal = 𝟙 _ := by
  let hground : QuarticNet.GroundTwistedCubicPresentation C.ideal :=
    QuarticNet.groundTwistedCubicPresentation_of_separableGeometricallyStandardTwistedCubic
      hgeo
  obtain ⟨e, he, hsmooth, s, hs⟩ :=
    QuarticNet.twistedCubic_descent_separable_overBase hgeo
  exact ⟨hground, e, he, hsmooth, s, hs⟩

/-- The homogeneous-Proj form of `lem:twisted-cubic`: the embedded curve is
the projective line and its ambient closed immersion is a twisted cubic. -/
theorem twisted_cubic (C : EmbeddedGeometricallyStandardTwistedCubic k) [PerfectField k] :
    C.IsTwistedCubic ∧
      ∃ e : C.curve ≅ projectiveLineProj k,
        e.hom ≫ projectiveLineProjToBase k = toBase C.ideal ∧
          Smooth (toBase C.ideal) ∧
            ∃ s : Spec (.of k) ⟶ C.curve, s ≫ toBase C.ideal = 𝟙 _ := by
  simpa only [IsTwistedCubic] using C.descent_perfect

end EmbeddedGeometricallyStandardTwistedCubic

/-- A reduced curve embedded as a closed subscheme of `P³`, for which the
homogeneous vanishing ideal of the actual embedding becomes a standard
twisted cubic over an algebraic closure.  Unlike
`ProjectiveCurveWithTwistedCubicPresentation`, this contains no chosen
homogeneous presentation: it is reconstructed from the embedding. -/
structure ReducedProjectiveCurveWithGeometricallyStandardTwistedCubic
    (k : Type u) [Field k] where
  curve : Scheme.{u}
  embedding : curve ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)
  embedding_closed : IsClosedImmersion embedding
  reduced : IsReduced curve
  geometricallyStandard :
    QuarticNet.GeometricallyStandardTwistedCubic
      (closedImmersionVanishingIdeal embedding)

namespace ReducedProjectiveCurveWithGeometricallyStandardTwistedCubic

variable {k : Type u} [Field k]

instance embedding_isClosedImmersion
    (C : ReducedProjectiveCurveWithGeometricallyStandardTwistedCubic k) :
    IsClosedImmersion C.embedding := C.embedding_closed

instance curve_isReduced
    (C : ReducedProjectiveCurveWithGeometricallyStandardTwistedCubic k) :
    IsReduced C.curve := C.reduced

/-- The canonically recovered homogeneous ideal of the given embedding. -/
noncomputable abbrev ideal
    (C : ReducedProjectiveCurveWithGeometricallyStandardTwistedCubic k) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k) :=
  closedImmersionVanishingIdeal C.embedding

/-- The coefficient-field structure morphism induced by the displayed
embedding into projective three-space. -/
noncomputable abbrev toBase
    (C : ReducedProjectiveCurveWithGeometricallyStandardTwistedCubic k) :
    C.curve ⟶ Spec (.of k) :=
  C.embedding ≫ ambientToBase

/-- The ground-field coordinate form of the assertion that the displayed
embedding is a twisted cubic. -/
def IsTwistedCubic
    (C : ReducedProjectiveCurveWithGeometricallyStandardTwistedCubic k) : Prop :=
  QuarticNet.GroundTwistedCubicPresentation C.ideal

/-- The reconstructed homogeneous presentation respects the coefficient-field
structure morphism induced by the original projective embedding. -/
theorem homogeneousRecoveryIso_hom_toBase
    (C : ReducedProjectiveCurveWithGeometricallyStandardTwistedCubic k) :
    (closedImmersionHomogeneousRecoveryIso C.embedding).hom ≫
      HomogeneousProjective.toBase C.ideal =
      C.toBase := by
  calc
    (closedImmersionHomogeneousRecoveryIso C.embedding).hom ≫
        HomogeneousProjective.toBase C.ideal =
        (closedImmersionHomogeneousRecoveryIso C.embedding).hom ≫
          (quotientProjMap C.ideal ≫ ambientToBase) := by
      rw [quotientProjMap_toBase]
    _ = ((closedImmersionHomogeneousRecoveryIso C.embedding).hom ≫
        quotientProjMap C.ideal) ≫ ambientToBase := Category.assoc _ _ _
    _ = C.toBase := by
      rw [closedImmersionHomogeneousRecoveryIso_hom_fac]

/-- The presentation-free, reduced form of `lem:twisted-cubic`.  The first
isomorphism reconstructs the curve and its displayed embedding from the
homogeneous vanishing ideal; the second identifies the curve with `P¹`. -/
theorem twisted_cubic
    (C : ReducedProjectiveCurveWithGeometricallyStandardTwistedCubic k)
    [PerfectField k] :
    C.IsTwistedCubic ∧
      ∃ r : C.curve ≅ scheme C.ideal,
        r.hom ≫ quotientProjMap C.ideal = C.embedding ∧
          ∃ e : C.curve ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = C.toBase ∧
              ∃ s : Spec (.of k) ⟶ C.curve, s ≫ C.toBase = 𝟙 _ := by
  obtain ⟨hground, e, he, -, s, hs⟩ :=
    EmbeddedGeometricallyStandardTwistedCubic.descent_perfect
      ⟨C.ideal, C.geometricallyStandard⟩
  let r := closedImmersionHomogeneousRecoveryIso C.embedding
  refine ⟨hground, r, closedImmersionHomogeneousRecoveryIso_hom_fac C.embedding,
    r ≪≫ e, ?_, s ≫ r.inv, ?_⟩
  · change (r.hom ≫ e.hom) ≫ projectiveLineProjToBase k = C.toBase
    rw [Category.assoc, he, homogeneousRecoveryIso_hom_toBase]
  · calc
      (s ≫ r.inv) ≫ C.toBase = s ≫ r.inv ≫ C.toBase := Category.assoc _ _ _
      _ = s ≫ r.inv ≫ (r.hom ≫ HomogeneousProjective.toBase C.ideal) := by
        rw [homogeneousRecoveryIso_hom_toBase]
      _ = s ≫ HomogeneousProjective.toBase C.ideal := by simp
      _ = 𝟙 _ := hs

/-- The arbitrary-field reduced form when the canonical ideal's coordinate
standardization is defined over the separable closure. -/
theorem twisted_cubic_separable
    (C : ReducedProjectiveCurveWithGeometricallyStandardTwistedCubic k)
    (hgeo : QuarticNet.SeparableGeometricallyStandardTwistedCubic C.ideal) :
    C.IsTwistedCubic ∧
      ∃ r : C.curve ≅ scheme C.ideal,
        r.hom ≫ quotientProjMap C.ideal = C.embedding ∧
          ∃ e : C.curve ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = C.toBase ∧
              ∃ s : Spec (.of k) ⟶ C.curve, s ≫ C.toBase = 𝟙 _ := by
  obtain ⟨hground, e, he, -, s, hs⟩ :=
    EmbeddedGeometricallyStandardTwistedCubic.descent_separable
      ⟨C.ideal, C.geometricallyStandard⟩ hgeo
  let r := closedImmersionHomogeneousRecoveryIso C.embedding
  refine ⟨hground, r, closedImmersionHomogeneousRecoveryIso_hom_fac C.embedding,
    r ≪≫ e, ?_, s ≫ r.inv, ?_⟩
  · change (r.hom ≫ e.hom) ≫ projectiveLineProjToBase k = C.toBase
    rw [Category.assoc, he, homogeneousRecoveryIso_hom_toBase]
  · calc
      (s ≫ r.inv) ≫ C.toBase = s ≫ r.inv ≫ C.toBase := Category.assoc _ _ _
      _ = s ≫ r.inv ≫ (r.hom ≫ HomogeneousProjective.toBase C.ideal) := by
        rw [homogeneousRecoveryIso_hom_toBase]
      _ = s ≫ HomogeneousProjective.toBase C.ideal := by simp
      _ = 𝟙 _ := hs

end ReducedProjectiveCurveWithGeometricallyStandardTwistedCubic

/-- A smooth curve embedded in projective three-space, whose canonical
homogeneous vanishing ideal is geometrically a standard twisted cubic.  This
is the presentation-free smooth hypothesis of `lem:twisted-cubic`, with the
geometric base-change condition expressed directly for the actual embedding. -/
structure SmoothProjectiveCurveWithGeometricallyStandardTwistedCubic
    (k : Type u) [Field k] where
  curve : Scheme.{u}
  embedding : curve ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)
  embedding_closed : IsClosedImmersion embedding
  smooth : Smooth (embedding ≫ ambientToBase)
  geometricallyStandard :
    QuarticNet.GeometricallyStandardTwistedCubic
      (closedImmersionVanishingIdeal embedding)

namespace SmoothProjectiveCurveWithGeometricallyStandardTwistedCubic

variable {k : Type u} [Field k]

instance embedding_isClosedImmersion
    (C : SmoothProjectiveCurveWithGeometricallyStandardTwistedCubic k) :
    IsClosedImmersion C.embedding := C.embedding_closed

/-- Smoothness over the coefficient field supplies the reducedness needed for
homogeneous-ideal recovery. -/
noncomputable def toReduced
    (C : SmoothProjectiveCurveWithGeometricallyStandardTwistedCubic k) :
    ReducedProjectiveCurveWithGeometricallyStandardTwistedCubic k where
  curve := C.curve
  embedding := C.embedding
  embedding_closed := C.embedding_closed
  reduced := by
    letI : Smooth (C.embedding ≫ ambientToBase) := C.smooth
    exact isReduced_of_smooth_toSpec_field (C.embedding ≫ ambientToBase)
  geometricallyStandard := C.geometricallyStandard

noncomputable abbrev ideal
    (C : SmoothProjectiveCurveWithGeometricallyStandardTwistedCubic k) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k) :=
  closedImmersionVanishingIdeal C.embedding

noncomputable abbrev toBase
    (C : SmoothProjectiveCurveWithGeometricallyStandardTwistedCubic k) :
    C.curve ⟶ Spec (.of k) :=
  C.embedding ≫ ambientToBase

def IsTwistedCubic
    (C : SmoothProjectiveCurveWithGeometricallyStandardTwistedCubic k) : Prop :=
  QuarticNet.GroundTwistedCubicPresentation C.ideal

/-- The smooth presentation-free form of `lem:twisted-cubic`.  It first
derives reducedness from smoothness, then invokes the recovered homogeneous
presentation of the actual embedding. -/
theorem twisted_cubic
    (C : SmoothProjectiveCurveWithGeometricallyStandardTwistedCubic k)
    [PerfectField k] :
    C.IsTwistedCubic ∧
      ∃ r : C.curve ≅ scheme C.ideal,
        r.hom ≫ quotientProjMap C.ideal = C.embedding ∧
          ∃ e : C.curve ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = C.toBase ∧
              ∃ s : Spec (.of k) ⟶ C.curve, s ≫ C.toBase = 𝟙 _ := by
  change C.toReduced.IsTwistedCubic ∧
    ∃ r : C.toReduced.curve ≅ scheme C.toReduced.ideal,
      r.hom ≫ quotientProjMap C.toReduced.ideal = C.toReduced.embedding ∧
        ∃ e : C.toReduced.curve ≅ projectiveLineProj k,
          e.hom ≫ projectiveLineProjToBase k = C.toReduced.toBase ∧
            ∃ s : Spec (.of k) ⟶ C.toReduced.curve,
              s ≫ C.toReduced.toBase = 𝟙 _
  exact C.toReduced.twisted_cubic

/-- The arbitrary-field smooth form when the canonical ideal's coordinate
standardization is defined over the separable closure. -/
theorem twisted_cubic_separable
    (C : SmoothProjectiveCurveWithGeometricallyStandardTwistedCubic k)
    (hgeo : QuarticNet.SeparableGeometricallyStandardTwistedCubic C.ideal) :
    C.IsTwistedCubic ∧
      ∃ r : C.curve ≅ scheme C.ideal,
        r.hom ≫ quotientProjMap C.ideal = C.embedding ∧
          ∃ e : C.curve ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = C.toBase ∧
              ∃ s : Spec (.of k) ⟶ C.curve, s ≫ C.toBase = 𝟙 _ := by
  change C.toReduced.IsTwistedCubic ∧
    ∃ r : C.toReduced.curve ≅ scheme C.toReduced.ideal,
      r.hom ≫ quotientProjMap C.toReduced.ideal = C.toReduced.embedding ∧
        ∃ e : C.toReduced.curve ≅ projectiveLineProj k,
          e.hom ≫ projectiveLineProjToBase k = C.toReduced.toBase ∧
            ∃ s : Spec (.of k) ⟶ C.toReduced.curve,
              s ≫ C.toReduced.toBase = 𝟙 _
  exact C.toReduced.twisted_cubic_separable hgeo

end SmoothProjectiveCurveWithGeometricallyStandardTwistedCubic

/-- Direct smooth-embedding form of twisted-cubic descent over a perfect
field.  Its sole geometric input is the coordinate certificate for the
canonical homogeneous vanishing ideal of the given embedded curve. -/
theorem smoothProjectiveCurve_twisted_cubic
    {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hgeo : QuarticNet.GeometricallyStandardTwistedCubic
      (closedImmersionVanishingIdeal i)) :
    QuarticNet.GroundTwistedCubicPresentation (closedImmersionVanishingIdeal i) ∧
      ∃ r : X ≅ scheme (closedImmersionVanishingIdeal i),
        r.hom ≫ quotientProjMap (closedImmersionVanishingIdeal i) = i ∧
          ∃ e : X ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = i ≫ ambientToBase ∧
              ∃ s : Spec (.of k) ⟶ X, s ≫ i ≫ ambientToBase = 𝟙 _ := by
  let C : SmoothProjectiveCurveWithGeometricallyStandardTwistedCubic k :=
    { curve := X
      embedding := i
      embedding_closed := inferInstance
      smooth := hsmooth
      geometricallyStandard := hgeo }
  exact C.twisted_cubic

/-- The actual coefficient base change of a smooth embedded curve is the Proj
of the coefficient extension of its canonical homogeneous ideal.  This is
the scheme-theoretic object denoted `Γ_{\bar k}` in `lem:twisted-cubic`. -/
noncomputable def smoothProjectiveCurveHomogeneousIdealBaseChangeIso
    {k L : Type u} [Field k] [Field L] (f : k →+* L)
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase)) :
    scheme (HomogeneousIdeal.map (ambientCoefficientGradedRingHom f)
      (closedImmersionVanishingIdeal i)) ≅
      pullback (i ≫ ambientToBase) (Spec.map (CommRingCat.ofHom f)) := by
  letI : Smooth (i ≫ ambientToBase) := hsmooth
  letI : IsReduced X := isReduced_of_smooth_toSpec_field (i ≫ ambientToBase)
  exact closedImmersionHomogeneousRecoveryBaseChangeIso f i

/-- If the coefficient extension of the canonical homogeneous ideal has a
ground-coordinate twisted-cubic presentation, then the actual categorical
base change of the embedded curve is isomorphic to the standard twisted
cubic.  This is the scheme-level form of the geometric hypothesis used in
the paper. -/
noncomputable def smoothProjectiveCurve_twistedCubicBaseChangeIso
    {k L : Type u} [Field k] [Field L] (f : k →+* L)
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hbar : IsTwistedCubicAfterCoefficientExtension f i) :
    pullback (i ≫ ambientToBase) (Spec.map (CommRingCat.ofHom f)) ≅
      scheme (QuarticNet.standardTwistedCubicHomogeneousIdeal (K := L)) := by
  let J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L) :=
    HomogeneousIdeal.map (ambientCoefficientGradedRingHom f)
      (closedImmersionVanishingIdeal i)
  have hbar' : QuarticNet.GroundTwistedCubicPresentation J := by
    exact hbar
  let M : GL (Fin 4) L := Classical.choose hbar'
  have hM := Classical.choose_spec hbar'
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) L).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have hIJ :
      (QuarticNet.standardTwistedCubicHomogeneousIdeal (K := L)).toIdeal =
        J.toIdeal.map (linearSubstitutionEquiv
          (M : Matrix (Fin 4) (Fin 4) L) hdet).toRingHom := by
    change QuarticNet.standardTwistedCubicIdeal L =
      J.toIdeal.map (linearSubstitutionEquiv
        (M : Matrix (Fin 4) (Fin 4) L) hdet).toRingHom
    exact hM.symm
  let eJ := linearCoordinateChangeSchemeIso
    (M : Matrix (Fin 4) (Fin 4) L) hdet J
      (QuarticNet.standardTwistedCubicHomogeneousIdeal (K := L)) hIJ
  let eBC := smoothProjectiveCurveHomogeneousIdealBaseChangeIso f i hsmooth
  exact eBC.symm ≪≫ eJ

/-- Perfect-field descent in the directly base-changed form.  The hypothesis
states that the coefficient extension of the canonical ideal of the embedded
curve is a standard twisted cubic over the algebraic closure; it is therefore
the homogeneous-coordinate formulation of the hypothesis in
`lem:twisted-cubic`. -/
theorem smoothProjectiveCurve_twisted_cubic_of_algebraicClosure_presentation
    {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hbar : IsTwistedCubicAfterCoefficientExtension
      (algebraMap k (AlgebraicClosure k)) i) :
    QuarticNet.GroundTwistedCubicPresentation (closedImmersionVanishingIdeal i) ∧
      ∃ r : X ≅ scheme (closedImmersionVanishingIdeal i),
        r.hom ≫ quotientProjMap (closedImmersionVanishingIdeal i) = i ∧
          ∃ e : X ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = i ≫ ambientToBase ∧
              ∃ s : Spec (.of k) ⟶ X, s ≫ i ≫ ambientToBase = 𝟙 _ := by
  exact smoothProjectiveCurve_twisted_cubic i hsmooth
    (geometricallyStandardTwistedCubic_of_algebraicClosure_groundPresentation hbar)

/-- The literal embedded form of `lem:twisted-cubic` needed in the
perfect-field degree-four argument.  The premise says that the actual
algebraic-closure base change of the displayed closed immersion is a standard
twisted cubic; the conclusion identifies the original curve with `P¹` and
exhibits a ground-field linear coordinate presentation of its embedding. -/
theorem paper_twisted_cubic_perfect
    {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hbar : IsTwistedCubicAfterCoefficientExtension
      (algebraMap k (AlgebraicClosure k)) i) :
    QuarticNet.GroundTwistedCubicPresentation (closedImmersionVanishingIdeal i) ∧
      ∃ e : X ≅ projectiveLineProj k,
        e.hom ≫ projectiveLineProjToBase k = i ≫ ambientToBase := by
  obtain ⟨hground, -, -, e, he, -, -⟩ :=
    smoothProjectiveCurve_twisted_cubic_of_algebraicClosure_presentation i hsmooth hbar
  exact ⟨hground, e, he⟩

/-- Direct arbitrary-field form when the canonical ideal's coordinate
standardization is defined over the separable closure. -/
theorem smoothProjectiveCurve_twisted_cubic_separable
    {k : Type u} [Field k]
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hgeo : QuarticNet.SeparableGeometricallyStandardTwistedCubic
      (closedImmersionVanishingIdeal i)) :
    QuarticNet.GroundTwistedCubicPresentation (closedImmersionVanishingIdeal i) ∧
      ∃ r : X ≅ scheme (closedImmersionVanishingIdeal i),
        r.hom ≫ quotientProjMap (closedImmersionVanishingIdeal i) = i ∧
          ∃ e : X ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = i ≫ ambientToBase ∧
              ∃ s : Spec (.of k) ⟶ X, s ≫ i ≫ ambientToBase = 𝟙 _ := by
  let hground :=
    QuarticNet.groundTwistedCubicPresentation_of_separableGeometricallyStandardTwistedCubic
      hgeo
  let C : SmoothProjectiveCurveWithGeometricallyStandardTwistedCubic k :=
    { curve := X
      embedding := i
      embedding_closed := inferInstance
      smooth := hsmooth
      geometricallyStandard :=
        groundTwistedCubicPresentation_geometricallyStandard hground }
  exact C.twisted_cubic_separable hgeo

/-- A scheme embedded as a closed projective subscheme of `P³`, together with
its homogeneous-Proj presentation and algebraic-closure twisted-cubic
coordinate certificate. -/
structure ProjectiveCurveWithTwistedCubicPresentation (k : Type u) [Field k] where
  curve : Scheme.{u}
  toBase : curve ⟶ Spec (.of k)
  embedding : curve ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)
  embedding_closed : IsClosedImmersion embedding
  smooth : Smooth toBase
  ideal : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k)
  presentation : curve ≅ scheme ideal
  presentation_toBase : presentation.hom ≫ HomogeneousProjective.toBase ideal = toBase
  presentation_embedding : presentation.hom ≫ quotientProjMap ideal = embedding
  geometricallyStandard : QuarticNet.GeometricallyStandardTwistedCubic ideal

namespace ProjectiveCurveWithTwistedCubicPresentation

variable {k : Type u} [Field k]

/-- The conclusion that the displayed ambient embedding is a twisted cubic,
expressed through its homogeneous presentation. -/
def IsTwistedCubic (C : ProjectiveCurveWithTwistedCubicPresentation k) : Prop :=
  QuarticNet.GroundTwistedCubicPresentation C.ideal

/-- The canonical homogeneous vanishing ideal of the displayed closed
immersion has the same projective zero locus as its supplied homogeneous
presentation.  Thus the ideal-sheaf and homogeneous-ideal descriptions agree
on the underlying embedded closed subset; the remaining recovery issue is
scheme-theoretic rather than topological. -/
theorem vanishingIdeal_zeroLocus_eq_presentation_zeroLocus
    (C : ProjectiveCurveWithTwistedCubicPresentation k) :
    ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 4) k)
      (closedImmersionVanishingIdeal C.embedding).toIdeal =
      ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 4) k)
        C.ideal.toIdeal := by
  letI : IsClosedImmersion C.embedding := C.embedding_closed
  have h₁ : ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 4) k)
      (closedImmersionVanishingIdeal C.embedding).toIdeal =
      Set.range (fun y => (C.embedding y : ProjectiveSpectrum
        (MvPolynomial.homogeneousSubmodule (Fin 4) k))) := by
    exact zeroLocus_closedImmersionVanishingIdeal C.embedding
  have h₂ : Set.range (fun y => (C.embedding y : ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin 4) k))) =
      Set.range (fun z => ((quotientProjMap C.ideal) z : ProjectiveSpectrum
        (MvPolynomial.homogeneousSubmodule (Fin 4) k))) := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy⟩
      refine ⟨C.presentation.hom y, ?_⟩
      rw [← hy]
      change (C.presentation.hom ≫ quotientProjMap C.ideal) y = C.embedding y
      rw [C.presentation_embedding]
    · rintro x ⟨z, hz⟩
      refine ⟨C.presentation.inv z, ?_⟩
      rw [← hz]
      change C.embedding (C.presentation.inv z) = (quotientProjMap C.ideal) z
      rw [← C.presentation_embedding]
      simp
  exact h₁.trans (h₂.trans (range_quotientProjMap C.ideal))

/-- Over a perfect field, the displayed ideal in a geometrically standard
twisted-cubic presentation is exactly the canonical homogeneous vanishing
ideal of its actual ambient embedding. -/
theorem vanishingIdeal_eq_presentation_perfect
    (C : ProjectiveCurveWithTwistedCubicPresentation k) [PerfectField k] :
    closedImmersionVanishingIdeal C.embedding = C.ideal := by
  exact closedImmersionVanishingIdeal_eq_of_groundTwistedCubicPresentation
    (QuarticNet.groundTwistedCubicPresentation_of_geometricallyStandardTwistedCubic
      C.geometricallyStandard)
    C.embedding C.presentation C.presentation_embedding

/-- The same identification over an arbitrary field when the coordinate
standardization is defined over the separable closure. -/
theorem vanishingIdeal_eq_presentation_separable
    (C : ProjectiveCurveWithTwistedCubicPresentation k)
    (hgeo : QuarticNet.SeparableGeometricallyStandardTwistedCubic C.ideal) :
    closedImmersionVanishingIdeal C.embedding = C.ideal := by
  exact closedImmersionVanishingIdeal_eq_of_groundTwistedCubicPresentation
    (QuarticNet.groundTwistedCubicPresentation_of_separableGeometricallyStandardTwistedCubic
      hgeo)
    C.embedding C.presentation C.presentation_embedding

/-- Scheme-level homogeneous-presentation form of `lem:twisted-cubic`.  The
only datum not constructed here is the homogeneous presentation of an
arbitrary closed immersion. -/
theorem twisted_cubic (C : ProjectiveCurveWithTwistedCubicPresentation k) [PerfectField k] :
    C.IsTwistedCubic ∧
      ∃ e : C.curve ≅ projectiveLineProj k,
        e.hom ≫ projectiveLineProjToBase k = C.toBase ∧
          ∃ s : Spec (.of k) ⟶ C.curve, s ≫ C.toBase = 𝟙 _ := by
  obtain ⟨hground, e, he, -, s, hs⟩ :=
    EmbeddedGeometricallyStandardTwistedCubic.descent_perfect
      ⟨C.ideal, C.geometricallyStandard⟩
  refine ⟨hground, C.presentation ≪≫ e, ?_, ?_⟩
  · change (C.presentation.hom ≫ e.hom) ≫ projectiveLineProjToBase k = C.toBase
    rw [Category.assoc, he, C.presentation_toBase]
  · refine ⟨s ≫ C.presentation.inv, ?_⟩
    calc
      (s ≫ C.presentation.inv) ≫ C.toBase =
          s ≫ C.presentation.inv ≫ C.toBase := Category.assoc _ _ _
      _ = s ≫ C.presentation.inv ≫
          (C.presentation.hom ≫ HomogeneousProjective.toBase C.ideal) := by
        rw [C.presentation_toBase]
      _ = s ≫ HomogeneousProjective.toBase C.ideal := by simp
      _ = 𝟙 _ := hs

end ProjectiveCurveWithTwistedCubicPresentation
end AllCharacteristics
