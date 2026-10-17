import PfaffianDescent.SerreExtensionFoundation
import PfaffianDescent.ProjectiveLineSmooth
import PfaffianDescent.ProjectiveLineConnected
import AllCharacteristics.FiniteSubschemeRationalCycleFamily
import AllCharacteristics.FiniteSubschemeFromImmersion
import AllCharacteristics.FlatIdealSubscheme
import AllCharacteristics.FlatPrincipalQuotient
import AllCharacteristics.RegularPairDimension
import AllCharacteristics.SmoothRegularity
import AllCharacteristics.OverlapCompositionGluing
import AllCharacteristics.SchemeGlueDataDescent
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import AllCharacteristics.HypersurfaceJacobianSmooth

/-!
# Affine charts for the projective-line Serre pencil

The rank-two Serre construction is expressed on affine trivializations of
the bundle, while the pencil is parameterized by the standard projective
line.  This file forms their product cover.  Every chart is affine, so the
local zero ideals can be calculated there and then compared on overlaps.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open scoped nonZeroDivisors

universe u

namespace SerreExtensionData

section

variable {K : Type u} [CommRing K] {X : Scheme.{u}}
  {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
  (f : X ⟶ Spec (.of K))

attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

/-- The product of the rank-two trivializing cover and the two standard
projective-line charts covers the ambient space of the Serre pencil. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineOpenCover
    (C : SerreExtensionRankTwoAffineCover e) :
    (projectiveLineAmbient K f).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight C.openCover (lineProjOpenCover K)
    f (projectiveLineProjToBase K)

/-- Each chart of the Serre-pencil parameter space is affine.  It is the
fiber product over the coefficient base of an affine rank-two trivialization
and a standard affine chart of the projective line. -/
instance SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_affine
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsAffine ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij) := by
  change IsAffine (pullback ((C.U ij.1).ι ≫ f)
    ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K))
  letI : IsAffine (C.U ij.1 : Scheme.{u}) := C.affine ij.1
  letI : IsAffine ((lineProjOpenCover K).X ij.2) := by
    change IsAffine (Spec _)
    infer_instance
  infer_instance

/-- The projective-line ambient product is separated when the original
surface is separated.  The projective-line structural map is proper, hence
separated, and separatedness is stable under base change and composition. -/
theorem projectiveLineAmbient_isSeparated [IsSeparated f] :
    (projectiveLineAmbient K f).IsSeparated := by
  constructor
  change IsSeparated (terminal.from (pullback f (projectiveLineProjToBase K)))
  have hcomp : terminal.from (pullback f (projectiveLineProjToBase K)) =
      pullback.fst f (projectiveLineProjToBase K) ≫ f ≫
        terminal.from (Spec (.of K)) := by
    ext
  rw [hcomp]
  letI : IsSeparated (projectiveLineProjToBase K) := by
    exact @IsProper.toIsSeparated _ _ _
      (AllCharacteristics.HomogeneousProjective.isProper_toBase
        (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)))
  infer_instance

/-- An open immersion from an affine scheme into a separated scheme is an
affine morphism. -/
theorem isAffineHom_openImmersion_of_affine_separated
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) [IsOpenImmersion g]
    [IsAffine Y] [Z.IsSeparated] : IsAffineHom g := by
  constructor
  intro U hU
  rw [← g.isAffineOpen_iff_of_isOpenImmersion,
    g.image_preimage_eq_opensRange_inf]
  exact (isAffineOpen_opensRange g).inf hU

/-- Projection of a product chart onto its chosen rank-two trivializing
open.  This is the base change of the corresponding standard affine
projective-line chart. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij ⟶
      (C.U ij.1 : Scheme.{u}) :=
  pullback.fst ((C.U ij.1).ι ≫ f)
    ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K)

/-- Projection of a product chart to its standard affine chart on the
parameter line. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij ⟶
      (lineProjOpenCover K).X ij.2 :=
  pullback.snd ((C.U ij.1).ι ≫ f)
    ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K)

/-- If the original family is flat, each product chart is flat over its
parameter-line chart: it is the base change of the restricted family. -/
theorem SerreExtensionRankTwoAffineCover.flat_projectiveLineOpenCover_toLineChart
    [Flat f] (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    Flat (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
  change Flat (pullback.snd ((C.U ij.1).ι ≫ f)
    ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K))
  infer_instance

/-- A relative-smooth surface remains smooth of the same relative dimension
on every product chart over a standard affine chart of the parameter line. -/
theorem
    SerreExtensionRankTwoAffineCover.smoothOfRelativeDimension_two_projectiveLineOpenCover_toLineChart
    [SmoothOfRelativeDimension 2 f] (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SmoothOfRelativeDimension 2
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
  change SmoothOfRelativeDimension 2 (pullback.snd ((C.U ij.1).ι ≫ f)
    ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K))
  letI : IsOpenImmersion (C.U ij.1).ι := inferInstance
  letI : SmoothOfRelativeDimension 0 (C.U ij.1).ι := inferInstance
  letI : SmoothOfRelativeDimension 2 ((C.U ij.1).ι ≫ f) := by
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + 2) ((C.U ij.1).ι ≫ f))
  letI : MorphismProperty.IsStableUnderBaseChangeAlong (@SmoothOfRelativeDimension 2)
      ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K) :=
    { of_isPullback := (smoothOfRelativeDimension_isStableUnderBaseChange 2).of_isPullback }
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The map from a product chart to the ambient parameter space, followed by
projection to the surface, is the chart projection to the selected affine
open followed by its open immersion into the surface. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toScheme
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij ≫
        projectiveLineAmbientToScheme K f =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij ≫
        (C.U ij.1).ι := by
  rcases ij with ⟨i, j⟩
  change (Scheme.Pullback.openCoverOfLeftRight C.openCover (lineProjOpenCover K)
    f (projectiveLineProjToBase K)).f (i, j) ≫ pullback.fst f (projectiveLineProjToBase K) =
      pullback.fst ((C.U i).ι ≫ f)
        ((lineProjOpenCover K).f j ≫ projectiveLineProjToBase K) ≫ (C.U i).ι
  rw [Scheme.Pullback.openCoverOfLeftRight_f]
  change pullback.lift _ _ _ ≫ pullback.fst f (projectiveLineProjToBase K) = _
  erw [pullback.lift_fst]
  rfl

/-- The parameter-line component of a product-chart inclusion is exactly the
standard chart inclusion after projection to that affine line chart. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLine
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij ≫
        projectiveLineAmbientToLine K f =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij ≫
        (lineProjOpenCover K).f ij.2 := by
  rcases ij with ⟨i, j⟩
  change (Scheme.Pullback.openCoverOfLeftRight C.openCover (lineProjOpenCover K)
    f (projectiveLineProjToBase K)).f (i, j) ≫
      pullback.snd f (projectiveLineProjToBase K) =
    pullback.snd ((C.U i).ι ≫ f)
      ((lineProjOpenCover K).f j ≫ projectiveLineProjToBase K) ≫
        (lineProjOpenCover K).f j
  rw [Scheme.Pullback.openCoverOfLeftRight_f]
  change pullback.lift _ _ _ ≫ pullback.snd f (projectiveLineProjToBase K) = _
  erw [pullback.lift_snd]
  rfl

/-- The intersection of two arbitrary affine product charts in the
projective-line parameter space.  Unlike the specialized overlap below, the
two charts may use different Serre trivializations. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) : Scheme.{u} :=
  pullback
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)

/-- Arbitrary intersections of affine product charts are affine when the
surface is separated.  This is the common affine setting for the remaining
comparison of distinct Serre trivializations. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_affine
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsAffine (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
      f C ij kl) := by
  letI : (projectiveLineAmbient K f).IsSeparated := projectiveLineAmbient_isSeparated f
  letI : IsAffine ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_affine f C ij
  letI : IsAffine ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X kl) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_affine f C kl
  letI : IsOpenImmersion
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).map_prop _
  letI : IsAffineHom
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) :=
    isAffineHom_openImmersion_of_affine_separated _
  infer_instance

/-- The left projection from a general product-chart intersection is an open
immersion. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_isOpenImmersion
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenImmersion (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) := by
  letI : IsOpenImmersion
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).map_prop _
  infer_instance

/-- The right projection from a general product-chart intersection is an open
immersion. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_snd_isOpenImmersion
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenImmersion (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) := by
  letI : IsOpenImmersion
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).map_prop _
  infer_instance

/-- The map from a general product-chart intersection to the affine Serre
chart used by its left member. -/
noncomputable abbrev
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl ⟶
      (C.U ij.1 : Scheme.{u}) :=
  pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) ≫
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij

/-- The map from a general product-chart intersection to the affine Serre
chart used by its right member. -/
noncomputable abbrev
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl ⟶
      (C.U kl.1 : Scheme.{u}) :=
  pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) ≫
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C kl

/-- The two local-chart maps from a general product-chart intersection have
the same composite to the original surface. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_toScheme_condition
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
      f C ij kl ≫ (C.U ij.1).ι =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
      f C ij kl ≫ (C.U kl.1).ι := by
  change
    (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij) ≫
        (C.U ij.1).ι =
    (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C kl) ≫
        (C.U kl.1).ι
  rw [Category.assoc,
    ← SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toScheme f C ij,
    ← Category.assoc, pullback.condition, Category.assoc,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toScheme f C kl]
  simp only [Category.assoc]

/-- The map from a general product-chart intersection to the overlap of its
two underlying Serre trivializations. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl ⟶
      ((C.U ij.1 ⊓ C.U kl.1 : X.Opens) : Scheme.{u}) :=
  (AlgebraicGeometry.isPullback_opens_inf (C.U ij.1) (C.U kl.1)).lift
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
      f C ij kl)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
      f C ij kl)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_toScheme_condition
      f C ij kl)

/-- The preceding factorization recovers the left local-chart map. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_left
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
      f C ij kl ≫ X.homOfLE (show C.U ij.1 ⊓ C.U kl.1 ≤ C.U ij.1 from inf_le_left) =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
      f C ij kl := by
  exact (AlgebraicGeometry.isPullback_opens_inf (C.U ij.1) (C.U kl.1)).lift_fst _ _ _

/-- The preceding factorization recovers the right local-chart map. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_right
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
      f C ij kl ≫ X.homOfLE (show C.U ij.1 ⊓ C.U kl.1 ≤ C.U kl.1 from inf_le_right) =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
      f C ij kl := by
  exact (AlgebraicGeometry.isPullback_opens_inf (C.U ij.1) (C.U kl.1)).lift_snd _ _ _

/-- The parameter-line map from a general product-chart overlap through its
left chart. -/
noncomputable abbrev
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLineChart
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl ⟶
      (lineProjOpenCover K).X ij.2 :=
  pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) ≫
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij

/-- The parameter-line map from a general product-chart overlap through its
right chart. -/
noncomputable abbrev
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLineChart
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl ⟶
      (lineProjOpenCover K).X kl.2 :=
  pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) ≫
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C kl

/-- The two parameter-line maps of a general product-chart overlap agree
after the affine line-chart inclusions. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_toLine_condition
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLineChart
      f C ij kl ≫ (lineProjOpenCover K).f ij.2 =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLineChart
      f C ij kl ≫ (lineProjOpenCover K).f kl.2 := by
  change
    (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) ≫
        (lineProjOpenCover K).f ij.2 =
    (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C kl) ≫
        (lineProjOpenCover K).f kl.2
  rw [Category.assoc,
    ← SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLine f C ij,
    ← Category.assoc, pullback.condition, Category.assoc,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLine f C kl]
  rfl

/-- The inverse projective-coordinate transition scalar on a general
product-chart overlap. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    Γ(SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl, ⊤) :=
  affineFunctionHom
    ((isPullback_chartOverlap I₀ ij.2 kl.2).lift
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLineChart
        f C ij kl)
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLineChart
        f C ij kl)
      (by
        change
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLineChart
            f C ij kl ≫ chartι I₀ ij.2 =
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLineChart
            f C ij kl ≫ chartι I₀ kl.2
        exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_toLine_condition
          f C ij kl))
    (↑((chartOverlapUnit I₀ ij.2 kl.2)⁻¹))

/-- The coordinate-transition scalar is a unit on every general
product-chart overlap. -/
theorem SerreExtensionRankTwoAffineCover.isUnit_projectiveLineOpenCoverGeneralOverlapUnit
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsUnit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit f C ij kl) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
  exact ((chartOverlapUnit I₀ ij.2 kl.2)⁻¹).isUnit.map (affineFunctionHom _)

/-- The scalar endomorphism induced by the general projective-coordinate
transition is invertible. -/
theorem
    SerreExtensionRankTwoAffineCover.isIso_projectiveLineOpenCoverGeneralOverlapUnitCoefficient
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsIso (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit f C ij kl)) :=
  BundleSectionZeroLocus.isIso_unitEndomorphismOfRegularFunction_of_isUnit _
    (SerreExtensionRankTwoAffineCover.isUnit_projectiveLineOpenCoverGeneralOverlapUnit
      f C ij kl)

/-- The left normalized projective coordinate on a general product-chart
overlap, represented as a unit-module endomorphism. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) (m : Bool) :
    SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
          f C ij kl).ringCatSheaf :=
  BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
    (affineFunctionHom
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLineChart
        f C ij kl)
      (chartCoordinate I₀ ij.2 m))

/-- The right normalized projective coordinate on a general product-chart
overlap, represented as a unit-module endomorphism. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) (m : Bool) :
    SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
          f C ij kl).ringCatSheaf :=
  BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
    (affineFunctionHom
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLineChart
        f C ij kl)
      (chartCoordinate I₀ kl.2 m))

/-- The standard projective transition rescales each homogeneous coordinate
by the same scalar on a general product-chart overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_coordinateCoefficient_relation
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) (m : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
      f C ij kl m =
      BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit f C ij kl) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
          f C ij kl m := by
  unfold
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
  rw [← BundleSectionZeroLocus.unitEndomorphismOfRegularFunction_mul]
  congr 1
  exact lineProjChartCoordinate_overlap_relation K ij.2 kl.2 m _ _ (by
    change
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLineChart
        f C ij kl ≫ chartι I₀ ij.2 =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLineChart
        f C ij kl ≫ chartι I₀ kl.2
    exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_toLine_condition
      f C ij kl)

/-- The distinguished left homogeneous coordinate is one on its own affine
parameter chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_leftCoordinateCoefficient_self
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
      f C ij kl ij.2 = 𝟙 _ := by
  rcases ij with ⟨i, b⟩
  cases b <;>
    unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient <;>
    rw [chartCoordinate_self, map_one,
      BundleSectionZeroLocus.unitEndomorphismOfRegularFunction_one]

/-- The distinguished right homogeneous coordinate is one on its own affine
parameter chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_rightCoordinateCoefficient_self
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
      f C ij kl kl.2 = 𝟙 _ := by
  rcases kl with ⟨j, c⟩
  cases c <;>
    unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient <;>
    rw [chartCoordinate_self, map_one,
      BundleSectionZeroLocus.unitEndomorphismOfRegularFunction_one]

/-- The common map from a general product-chart intersection to the original
surface, written through the left Serre trivialization. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl ⟶ X :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
    f C ij kl ≫ (C.U ij.1).ι

/-- The global Serre bundle pulled to a general product-chart intersection
has canonically equivalent left and right local presentations. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapGlobalModuleIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme
        f C ij kl)).obj e.E ≅
    (AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
        f C ij kl ≫ (C.U kl.1).ι)).obj e.E :=
  (AlgebraicGeometry.Scheme.Modules.pullbackCongr
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_toScheme_condition
      f C ij kl)).app e.E

/-- The intersection, over the projective-line parameter space, of two
product charts based on the same Serre trivialization. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) : Scheme.{u} :=
  pullback
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))

/-- Intersections of the affine product charts are affine once the original
surface is separated.  This supplies the affine hypothesis required to
compare their coordinate zero ideals by restriction. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_affine
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (i : C.ι) (b c : Bool) :
    IsAffine (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c) := by
  exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_affine
    f C (i, b) (i, c)

/-- The map from the parameter-chart intersection to its left affine
projective-line chart. -/
noncomputable abbrev
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLeftLineChart
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c ⟶
      (lineProjOpenCover K).X b :=
  pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) ≫
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C (i, b)

/-- The map from the parameter-chart intersection to its right affine
projective-line chart. -/
noncomputable abbrev
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLineChart
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c ⟶
      (lineProjOpenCover K).X c :=
  pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) ≫
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C (i, c)

/-- The two maps from a product-chart intersection to the projective line
are equal after their affine chart inclusions. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_toLine_condition
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLeftLineChart
      f C i b c ≫ (lineProjOpenCover K).f b =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLineChart
      f C i b c ≫ (lineProjOpenCover K).f c := by
  change
    (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C (i, b)) ≫
        (lineProjOpenCover K).f b =
    (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C (i, c)) ≫
        (lineProjOpenCover K).f c
  rw [Category.assoc,
    ← SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLine f C
      ((show C.openCover.I₀ from i), b),
    ← Category.assoc, pullback.condition, Category.assoc,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLine f C
      ((show C.openCover.I₀ from i), c)]
  rfl

/-- On the self-overlap of one parameter chart, the two projections to that
chart agree.  The statement is obtained by cancelling the chart's open
immersion after the pullback relation above. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_toLine_eq_of_eq
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLeftLineChart
      f C i b b =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLineChart
        f C i b b := by
  letI : IsOpenImmersion ((lineProjOpenCover K).f b) :=
    (lineProjOpenCover K).map_prop _
  apply (cancel_mono ((lineProjOpenCover K).f b)).mp
  exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_toLine_condition
    f C i b b

/-- The actual transition rule for every normalized homogeneous coordinate on
the intersection of two product charts. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_coordinate_relation
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c m : Bool) :
    affineFunctionHom
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLeftLineChart
        f C i b c)
      (chartCoordinate I₀ b m) =
    affineFunctionHom
        ((isPullback_chartOverlap I₀ b c).lift
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLeftLineChart
            f C i b c)
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLineChart
            f C i b c)
          (by
            change
              SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLeftLineChart
                f C i b c ≫ chartι I₀ b =
              SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLineChart
                f C i b c ≫ chartι I₀ c
            exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_toLine_condition
              f C i b c))
        (↑((chartOverlapUnit I₀ b c)⁻¹)) *
      affineFunctionHom
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLineChart
          f C i b c)
        (chartCoordinate I₀ c m) := by
  exact lineProjChartCoordinate_overlap_relation K b c m _ _ (by
    change
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLeftLineChart
        f C i b c ≫ chartι I₀ b =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLineChart
        f C i b c ≫ chartι I₀ c
    exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_toLine_condition
      f C i b c)

/-- The inverse projective-coordinate ratio, pulled back to a product-chart
intersection. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    Γ(SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c, ⊤) :=
  affineFunctionHom
    ((isPullback_chartOverlap I₀ b c).lift
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLeftLineChart
        f C i b c)
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLineChart
        f C i b c)
      (by
        change
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLeftLineChart
            f C i b c ≫ chartι I₀ b =
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLineChart
            f C i b c ≫ chartι I₀ c
        exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_toLine_condition
          f C i b c))
    (↑((chartOverlapUnit I₀ b c)⁻¹))

/-- The projective-coordinate transition scalar is a unit on the actual
product-chart intersection. -/
theorem SerreExtensionRankTwoAffineCover.isUnit_projectiveLineOpenCoverOverlapUnit
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsUnit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit f C i b c) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit
  exact ((chartOverlapUnit I₀ b c)⁻¹).isUnit.map (affineFunctionHom _)

/-- The unit-module endomorphism induced by the parameter transition scalar
is invertible. -/
theorem SerreExtensionRankTwoAffineCover.isIso_projectiveLineOpenCoverOverlapUnitCoefficient
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsIso (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit f C i b c)) :=
  BundleSectionZeroLocus.isIso_unitEndomorphismOfRegularFunction_of_isUnit _
    (SerreExtensionRankTwoAffineCover.isUnit_projectiveLineOpenCoverOverlapUnit f C i b c)

/-- A normalized projective coordinate on the left parameter chart, viewed
as a scalar endomorphism on the product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLeftCoordinateCoefficient
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c m : Bool) :
    SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c).ringCatSheaf :=
  BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
    (affineFunctionHom
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLeftLineChart
        f C i b c)
      (chartCoordinate I₀ b m))

/-- The corresponding normalized projective coordinate on the right
parameter chart. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c m : Bool) :
    SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c).ringCatSheaf :=
  BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
    (affineFunctionHom
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLineChart
        f C i b c)
      (chartCoordinate I₀ c m))

/-- The coordinate transition rule holds as an equality of scalar
endomorphisms, with the overlap unit acting by common rescaling. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_coordinateCoefficient_relation
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c m : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLeftCoordinateCoefficient
      f C i b c m =
      BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit f C i b c) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
          f C i b c m := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLeftCoordinateCoefficient
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
  rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_coordinate_relation,
    BundleSectionZeroLocus.unitEndomorphismOfRegularFunction_mul]
  rfl

/-- The distinguished normalized coordinate is one on the left product
chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_leftCoordinateCoefficient_self
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLeftCoordinateCoefficient
      f C i b c b = 𝟙 _ := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLeftCoordinateCoefficient
  rw [chartCoordinate_self, map_one,
    BundleSectionZeroLocus.unitEndomorphismOfRegularFunction_one]

/-- The distinguished normalized coordinate is one on the right product
chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_rightCoordinateCoefficient_self
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
      f C i b c c = 𝟙 _ := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
  rw [chartCoordinate_self, map_one,
    BundleSectionZeroLocus.unitEndomorphismOfRegularFunction_one]

/-- The two coordinate endomorphisms agree on the self-overlap of a single
parameter chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_coordinateCoefficient_eq_of_eq
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b m : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLeftCoordinateCoefficient
      f C i b b m =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
        f C i b b m := by
  unfold
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLeftCoordinateCoefficient
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
  rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_toLine_eq_of_eq
    f C i b]

/-- The normalized homogeneous coefficient pair induced from the left
parameter chart. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftCoefficients
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c).ringCatSheaf) ×
    (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c).ringCatSheaf) :=
  if b = true then
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLeftCoordinateCoefficient
      f C i b c (!b), 𝟙 _)
  else
    (𝟙 _, SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLeftCoordinateCoefficient
      f C i b c (!b))

/-- The normalized homogeneous coefficient pair induced from the right
parameter chart. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c).ringCatSheaf) ×
    (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c).ringCatSheaf) :=
  if c = true then
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
      f C i b c (!c), 𝟙 _)
  else
    (𝟙 _, SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
      f C i b c (!c))

/-- The normalized coefficient pairs agree on a self-overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedCoefficients_eq_of_eq
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftCoefficients
      f C i b b =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
        f C i b b := by
  by_cases hb : b = true
  · unfold
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftCoefficients
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
    rw [if_pos hb, if_pos hb,
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_coordinateCoefficient_eq_of_eq
        f C i b (!b)]
  · unfold
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftCoefficients
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
    rw [if_neg hb, if_neg hb,
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_coordinateCoefficient_eq_of_eq
        f C i b (!b)]

/-- On the overlap of the two distinct parameter charts, their normalized
homogeneous coefficient pairs differ by the invertible common transition
factor. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedCoefficients_commonScale
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool)
    (hbc : b ≠ c) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftCoefficients
      f C i b c =
      (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit f C i b c) ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
          f C i b c).1,
       BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit f C i b c) ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
          f C i b c).2) := by
  cases b <;> cases c
  · exact False.elim (hbc rfl)
  · change
      (𝟙 _,
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLeftCoordinateCoefficient
          f C i false true true) =
      (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit f C i false true) ≫
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
            f C i false true false,
        BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit f C i false true) ≫
          𝟙 _)
    apply Prod.ext
    · exact
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_leftCoordinateCoefficient_self
          f C i false true).symm.trans
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_coordinateCoefficient_relation
            f C i false true false)
    · simpa only [
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_rightCoordinateCoefficient_self,
        Category.comp_id] using
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_coordinateCoefficient_relation
            f C i false true true
  · change
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLeftCoordinateCoefficient
          f C i true false false,
        𝟙 _) =
      (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit f C i true false) ≫
          𝟙 _,
        BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit f C i true false) ≫
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
            f C i true false true)
    apply Prod.ext
    · simpa only [
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_rightCoordinateCoefficient_self,
        Category.comp_id] using
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_coordinateCoefficient_relation
            f C i true false false
    · exact
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_leftCoordinateCoefficient_self
          f C i true false).symm.trans
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_coordinateCoefficient_relation
            f C i true false true)
  · exact False.elim (hbc rfl)

/-- The projection from a product chart to its selected rank-two
trivialization is open.  It is the base change of the universally open
projective-line chart over the coefficient base. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_isOpenMap
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij) := by
  change IsOpenMap (pullback.fst ((C.U ij.1).ι ≫ f)
    ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K))
  letI : UniversallyOpen
      ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K) := inferInstance
  exact (pullback.fst ((C.U ij.1).ι ≫ f)
    ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K)).isOpenMap

/-- The left local-chart presentation from an arbitrary product-chart
intersection is open. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_isOpenMap
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
        f C ij kl) := by
  letI : IsOpenImmersion (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_isOpenImmersion
      f C ij kl
  exact
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_isOpenMap
      f C ij).comp
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)).isOpenMap

/-- The common map from a general product-chart overlap to the surface is
open. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme_isOpenMap
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme
        f C ij kl) := by
  change IsOpenMap
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
      f C ij kl ≫ (C.U ij.1).ι)
  letI : IsOpenImmersion (C.U ij.1).ι := inferInstance
  exact (C.U ij.1).ι.isOpenMap.comp
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_isOpenMap
      f C ij kl)

/-- Pullback of the unit module is invertible along the common map from a
general product-chart overlap to the surface. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme_pullbackUnitComparison_isIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme
        f C ij kl)) :=
  BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme_isOpenMap
      f C ij kl)

/-- The right local-chart presentation from an arbitrary product-chart
intersection is open. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_isOpenMap
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
        f C ij kl) := by
  letI : IsOpenImmersion (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_snd_isOpenImmersion
      f C ij kl
  exact
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_isOpenMap
      f C kl).comp
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)).isOpenMap

/-- Pullback of the unit module along the left local presentation on a
general intersection is invertible. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_pullbackUnitComparison_isIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
        f C ij kl)) :=
  BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_isOpenMap
      f C ij kl)

/-- Pullback of the unit module along the right local presentation on a
general intersection is invertible. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_pullbackUnitComparison_isIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
        f C ij kl)) :=
  BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_isOpenMap
      f C ij kl)

/-- The map from a product-chart intersection to the overlap of its two
Serre trivializations is open. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_isOpenMap
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
        f C ij kl) := by
  let h := X.homOfLE (show C.U ij.1 ⊓ C.U kl.1 ≤ C.U ij.1 from inf_le_left)
  let r := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
    f C ij kl
  haveI : IsOpenImmersion h := inferInstance
  have hp : IsOpenMap (r ≫ h) := by
    rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_left]
    exact
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_isOpenMap
        f C ij kl
  change IsOpenMap r
  exact h.isOpenEmbedding.isOpenMap_iff.mpr hp

/-- Pullback of the unit module along the map to the overlap of the two
Serre trivializations is invertible. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_pullbackUnitComparison_isIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
        f C ij kl)) :=
  BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_isOpenMap
      f C ij kl)

/-- Pullback of the unit module along the left inclusion of a general
product-chart intersection is invertible. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_pullbackUnitComparison_isIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))) := by
  letI : IsOpenImmersion (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_isOpenImmersion
      f C ij kl
  exact BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)).isOpenMap

/-- Pullback of the unit module along the right inclusion of a general
product-chart intersection is invertible. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_snd_pullbackUnitComparison_isIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))) := by
  letI : IsOpenImmersion (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_snd_isOpenImmersion
      f C ij kl
  exact BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)).isOpenMap

/-- The left projection from a parameter-chart intersection is open.  It is
the base change of the right-hand chart inclusion. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_fst_isOpenMap
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsOpenMap (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))) := by
  letI : IsOpenImmersion
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).map_prop _
  exact (pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))).isOpenMap

/-- The left projection from a parameter-chart intersection is the base
change of an open chart inclusion, hence is itself an open immersion. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_fst_isOpenImmersion
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsOpenImmersion (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))) := by
  letI : IsOpenImmersion
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).map_prop _
  infer_instance

instance SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_fst_isOpenImmersion_instance
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsOpenImmersion (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))) :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_fst_isOpenImmersion
    f C i b c

/-- The right projection from a parameter-chart intersection is likewise an
open immersion. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_isOpenImmersion
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsOpenImmersion (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))) := by
  letI : IsOpenImmersion
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b)) :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).map_prop _
  infer_instance

instance SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_isOpenImmersion_instance
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsOpenImmersion (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))) :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_isOpenImmersion
    f C i b c

/-- The right projection is open, as a consequence of its open-immersion
description. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_isOpenMap
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsOpenMap (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))) := by
  letI : IsOpenImmersion (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_isOpenImmersion
      f C i b c
  exact (pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))).isOpenMap

/-- Pullback of the unit module is invertible along the left inclusion of a
parameter-chart intersection. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_fst_pullbackUnitComparison_isIso
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))) :=
  BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_fst_isOpenMap
      f C i b c)

/-- The corresponding unit comparison is invertible along the right overlap
projection. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))) :=
  BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_isOpenMap
      f C i b c)

/-- The common map from a parameter-chart intersection to the fixed Serre
trivialization.  We use the left presentation; the next theorem proves that
the right presentation is the same map. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c ⟶
      (C.U i : Scheme.{u}) :=
  pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) ≫
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, b)

/-- The same map to the Serre trivialization, expressed through the right
parameter chart.  Keeping this presentation separate makes right-hand
pullback functoriality type-correct. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c ⟶
      (C.U i : Scheme.{u}) :=
  pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) ≫
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c)

/-- Both product charts induce the same map from their intersection to the
chosen affine Serre trivialization. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_toLocalScheme_eq
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme
      f C i b c =
    pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c) := by
  change
    pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, b) =
    pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c)
  apply (cancel_mono (C.U i).ι).mp
  rw [Category.assoc,
    ← SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toScheme f C
      ((show C.openCover.I₀ from i), b),
    ← Category.assoc, pullback.condition, Category.assoc,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toScheme f C
      ((show C.openCover.I₀ from i), c)]
  rfl

/-- The right presentation of the overlap-to-local map agrees with the
common left presentation. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_eq
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme
      f C i b c =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme
        f C i b c :=
  (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_toLocalScheme_eq
    f C i b c).symm

/-- The map from a parameter-chart intersection to the original surface,
expressed through its common Serre trivialization. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToScheme
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c ⟶ X :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme f C i b c ≫
    (C.U i).ι

/-- The overlap map to the surface can also be calculated through its left
product-chart inclusion. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_toScheme_eq_left
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToScheme f C i b c =
      pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) ≫
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b) ≫
          projectiveLineAmbientToScheme K f) := by
  change
    (pullback.fst _ _ ≫
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, b)) ≫
      (C.U i).ι =
    pullback.fst _ _ ≫
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b) ≫
        projectiveLineAmbientToScheme K f)
  rw [← Category.assoc]
  exact congrArg (fun q => pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)) ≫ q)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toScheme f C (i, b)).symm

/-- The common map from a chart intersection to the Serre trivialization is
open, so its pullback preserves the explicit free rank-two presentation. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme_isOpenMap
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsOpenMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme
        f C i b c) := by
  change IsOpenMap
    (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f
        ((show C.openCover.I₀ from i), b))
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f
        ((show C.openCover.I₀ from i), c)) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C
          ((show C.openCover.I₀ from i), b))
  letI : IsOpenImmersion
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f
        ((show C.openCover.I₀ from i), c)) :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).map_prop _
  exact
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_isOpenMap
      f C ((show C.openCover.I₀ from i), b)).comp
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f
          ((show C.openCover.I₀ from i), b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f
        ((show C.openCover.I₀ from i), c))).isOpenMap

/-- The right presentation of the overlap-to-local map is open as well. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_isOpenMap
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsOpenMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme
        f C i b c) := by
  exact
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_isOpenMap
      f C (i, c)).comp
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_isOpenMap
        f C i b c)

/-- Pullback of the unit module along the right presentation of the overlap
map is invertible. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_pullbackUnitComparison_isIso
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme
        f C i b c)) :=
  BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_isOpenMap
      f C i b c)

/-- The rank-two bundle, first restricted to a chosen affine trivialization
and then pulled to its product chart. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.projectiveLineLocalModule
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :=
  (AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij)).obj
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
        (e.E.over (C.U ij.1)))

/-- The module obtained by first restricting to a Serre trivialization and
then pulling to a parameter chart is canonically the pullback of the original
Serre bundle along that chart's map to the surface. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalModuleIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij ≫
          projectiveLineAmbientToScheme K f)).obj e.E := by
  rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toScheme f C ij]
  let p := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij
  let U := C.U ij.1
  exact
    (AlgebraicGeometry.Scheme.Modules.pullback p).mapIso
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app e.E ≪≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app e.E) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp p U.ι).app e.E

/-- The left local presentation of the rank-two bundle on an arbitrary
product-chart intersection. -/
noncomputable abbrev
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalModule
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :=
  (AlgebraicGeometry.Scheme.Modules.pullback
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
      f C ij kl)).obj
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
      (e.E.over (C.U ij.1)))

/-- The right local presentation of the rank-two bundle on an arbitrary
product-chart intersection. -/
noncomputable abbrev
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalModule
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :=
  (AlgebraicGeometry.Scheme.Modules.pullback
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
      f C ij kl)).obj
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
      (e.E.over (C.U kl.1)))

/-- The left local presentation is the pullback of the original Serre bundle
along the common map to the surface. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalModuleIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalModule
      f C ij kl ≅
    (AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme
        f C ij kl)).obj e.E := by
  let p := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
    f C ij kl
  let U := C.U ij.1
  exact
    (AlgebraicGeometry.Scheme.Modules.pullback p).mapIso
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app e.E ≪≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app e.E) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp p U.ι).app e.E

/-- The right local presentation is the pullback of the original Serre bundle
along its map to the surface. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalModuleIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalModule
      f C ij kl ≅
    (AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
        f C ij kl ≫ (C.U kl.1).ι)).obj e.E := by
  let p := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
    f C ij kl
  let U := C.U kl.1
  exact
    (AlgebraicGeometry.Scheme.Modules.pullback p).mapIso
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app e.E ≪≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app e.E) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp p U.ι).app e.E

/-- The two local rank-two presentations on any product-chart intersection
are canonically identified through the global Serre bundle. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLocalModuleIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalModule
      f C ij kl ≅
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalModule
      f C ij kl :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalModuleIso
    f C ij kl ≪≫
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapGlobalModuleIso
      f C ij kl ≪≫
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalModuleIso
      f C ij kl).symm

/-- The left local rank-two presentation remains explicitly free on an
arbitrary product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalFreeIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.free
      (R := (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl).ringCatSheaf)
      (ULift.{u} (Fin 2)) ≅
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalModule
      f C ij kl :=
  BundleSectionZeroLocus.pullbackFreeIsoOf_isOpenMap
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
      f C ij kl)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_isOpenMap
      f C ij kl)
    (ULift.{u} (Fin 2))
    (BundleSectionZeroLocus.localFreeIsoOfOver (C.U ij.1) (ULift.{u} (Fin 2))
      (C.trivialization ij.1))

/-- The right local rank-two presentation remains explicitly free on an
arbitrary product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalFreeIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.free
      (R := (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl).ringCatSheaf)
      (ULift.{u} (Fin 2)) ≅
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalModule
      f C ij kl :=
  BundleSectionZeroLocus.pullbackFreeIsoOf_isOpenMap
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
      f C ij kl)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_isOpenMap
      f C ij kl)
    (ULift.{u} (Fin 2))
    (BundleSectionZeroLocus.localFreeIsoOfOver (C.U kl.1) (ULift.{u} (Fin 2))
      (C.trivialization kl.1))

/-- The canonical Serre section on the left local presentation of a general
product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalCanonicalSection
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalModule
      f C ij kl).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
      f C ij kl)
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
      (e.E.over (C.U ij.1)))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_pullbackUnitComparison_isIso
      f C ij kl)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1) e.canonicalSection)

/-- The chosen lifted Serre section on the left local presentation of a
general product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalLiftSection
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalModule
      f C ij kl).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
      f C ij kl)
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
      (e.E.over (C.U ij.1)))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_pullbackUnitComparison_isIso
      f C ij kl)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1) seed.lift)

/-- The canonical Serre section on the right local presentation of a general
product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalCanonicalSection
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalModule
      f C ij kl).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
      f C ij kl)
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
      (e.E.over (C.U kl.1)))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_pullbackUnitComparison_isIso
      f C ij kl)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U kl.1) e.canonicalSection)

/-- The chosen lifted Serre section on the right local presentation of a
general product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalLiftSection
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalModule
      f C ij kl).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
      f C ij kl)
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
      (e.E.over (C.U kl.1)))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_pullbackUnitComparison_isIso
      f C ij kl)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U kl.1) seed.lift)

/-- The canonical Serre section pulled directly to a general product-chart
overlap through its common map to the surface. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapGlobalCanonicalSection
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme
        f C ij kl)).obj e.E).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme
      f C ij kl)
    e.E
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme_pullbackUnitComparison_isIso
      f C ij kl)
    e.canonicalSection

/-- The selected lifted Serre section pulled directly to a general
product-chart overlap through its common map to the surface. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapGlobalLiftSection
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme
        f C ij kl)).obj e.E).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme
      f C ij kl)
    e.E
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToScheme_pullbackUnitComparison_isIso
      f C ij kl)
    seed.lift

/-- The Serre bundle over the intersection of two trivializing opens, pulled
to an arbitrary product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLocalModule
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl).Modules :=
  (AlgebraicGeometry.Scheme.Modules.pullback
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
      f C ij kl)).obj
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1 ⊓ C.U kl.1)).functor.obj
      (e.E.over (C.U ij.1 ⊓ C.U kl.1)))

/-- A global Serre section restricted to the common trivializing overlap and
then pulled to a product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection
    (C : SerreExtensionRankTwoAffineCover e) (s : e.E.sections)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLocalModule
      f C ij kl).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
      f C ij kl)
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1 ⊓ C.U kl.1)).functor.obj
      (e.E.over (C.U ij.1 ⊓ C.U kl.1)))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_pullbackUnitComparison_isIso
      f C ij kl)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1 ⊓ C.U kl.1) s)

/-- The common overlap module is canonically the iterated pullback from the
left Serre trivialization. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToLeftCompositeModuleIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLocalModule
      f C ij kl ≅
    (AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
        f C ij kl ≫ X.homOfLE
          (show C.U ij.1 ⊓ C.U kl.1 ≤ C.U ij.1 from inf_le_left))).obj
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
        (e.E.over (C.U ij.1))) := by
  let h' : (C.U ij.1 ⊓ C.U kl.1) ⟶ C.U ij.1 := homOfLE inf_le_left
  let h := X.homOfLE (leOfHom h')
  let r := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
    f C ij kl
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
    (e.E.over (C.U ij.1))
  let g := BundleSectionZeroLocus.localRestrictionTargetIso (E := e.E) h'
  change (AlgebraicGeometry.Scheme.Modules.pullback r).obj
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1 ⊓ C.U kl.1)).functor.obj
      (e.E.over (C.U ij.1 ⊓ C.U kl.1))) ≅
    (AlgebraicGeometry.Scheme.Modules.pullback (r ≫ h)).obj E
  exact
    (AlgebraicGeometry.Scheme.Modules.pullback r).mapIso
      (g ≪≫ (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback h).app E) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp r h).app E

/-- Transporting a common-overlap section to the iterated pullback from the
left Serre trivialization agrees with first restricting it to that chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection_toLeftComposite
    (C : SerreExtensionRankTwoAffineCover e) (s : e.E.sections)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.sectionsMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToLeftCompositeModuleIso
        f C ij kl).hom
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection
        f C s ij kl) =
    BundleSectionZeroLocus.pullbackSection
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
        f C ij kl ≫ X.homOfLE
          (show C.U ij.1 ⊓ C.U kl.1 ≤ C.U ij.1 from inf_le_left))
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
        (e.E.over (C.U ij.1)))
      (by
        rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_left]
        exact
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_pullbackUnitComparison_isIso
            f C ij kl)
      (BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1) s) := by
  let h' : (C.U ij.1 ⊓ C.U kl.1) ⟶ C.U ij.1 := homOfLE inf_le_left
  let h := X.homOfLE (leOfHom h')
  let r := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
    f C ij kl
  let EW := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1 ⊓ C.U kl.1)).functor.obj
    (e.E.over (C.U ij.1 ⊓ C.U kl.1))
  let EU := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
    (e.E.over (C.U ij.1))
  let g := BundleSectionZeroLocus.localRestrictionTargetIso (E := e.E) h'
  let a := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback h).app EU
  let c := (AlgebraicGeometry.Scheme.Modules.pullbackComp r h).app EU
  let sw := BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1 ⊓ C.U kl.1) s
  let su := BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1) s
  let sr := BundleSectionZeroLocus.restrictModuleSection h EU su
  haveI : IsOpenImmersion h := inferInstance
  have hr : IsIso (BundleSectionZeroLocus.pullbackUnitComparison r) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_pullbackUnitComparison_isIso
      f C ij kl
  have hh : IsIso (BundleSectionZeroLocus.pullbackUnitComparison h) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _ h.isOpenMap
  have hcomp : r ≫ h =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
        f C ij kl :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_left
      f C ij kl
  have hrh : IsIso (BundleSectionZeroLocus.pullbackUnitComparison (r ≫ h)) := by
    rw [hcomp]
    exact
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_pullbackUnitComparison_isIso
        f C ij kl
  have hg : SheafOfModules.sectionsMap g.hom sw = sr := by
    have hcompat := BundleSectionZeroLocus.localRestrictionTargetIso_sectionCompatibility h' s
    calc
      SheafOfModules.sectionsMap g.hom sw =
        SheafOfModules.sectionsMap g.hom (SheafOfModules.sectionsMap g.inv sr) := by
          exact congrArg (SheafOfModules.sectionsMap g.hom) hcompat.symm
      _ = sr := BundleSectionZeroLocus.sectionsMap_hom_inv g sr
  have h1 : SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullback r).map g.hom)
      (BundleSectionZeroLocus.pullbackSection r EW hr sw) =
      BundleSectionZeroLocus.pullbackSection r
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor h).obj EU) hr sr := by
    rw [BundleSectionZeroLocus.sectionsMap_pullbackSection]
    rw [hg]
  have h2 : SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom)
      (BundleSectionZeroLocus.pullbackSection r
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor h).obj EU) hr sr) =
      BundleSectionZeroLocus.pullbackSection r
        ((AlgebraicGeometry.Scheme.Modules.pullback h).obj EU) hr
        (BundleSectionZeroLocus.pullbackSection h EU hh su) := by
    refine (BundleSectionZeroLocus.sectionsMap_pullbackSection r a.hom hr sr).trans ?_
    exact congrArg (fun q => BundleSectionZeroLocus.pullbackSection r
      ((AlgebraicGeometry.Scheme.Modules.pullback h).obj EU) hr q)
      (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection h hh su)
  have h3 : SheafOfModules.sectionsMap c.hom
      (BundleSectionZeroLocus.pullbackSection r
        ((AlgebraicGeometry.Scheme.Modules.pullback h).obj EU) hr
        (BundleSectionZeroLocus.pullbackSection h EU hh su)) =
      BundleSectionZeroLocus.pullbackSection (r ≫ h) EU hrh su := by
    have hc := BundleSectionZeroLocus.pullbackSection_comp r h EU hr hh hrh su
    calc
      SheafOfModules.sectionsMap c.hom
          (BundleSectionZeroLocus.pullbackSection r
            ((AlgebraicGeometry.Scheme.Modules.pullback h).obj EU) hr
            (BundleSectionZeroLocus.pullbackSection h EU hh su)) =
        SheafOfModules.sectionsMap c.hom
          (SheafOfModules.sectionsMap c.inv
            (BundleSectionZeroLocus.pullbackSection (r ≫ h) EU hrh su)) := by
              exact congrArg (SheafOfModules.sectionsMap c.hom) hc.symm
      _ = BundleSectionZeroLocus.pullbackSection (r ≫ h) EU hrh su :=
        BundleSectionZeroLocus.sectionsMap_hom_inv c _
  dsimp [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToLeftCompositeModuleIso,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLocalModule]
  rw [Functor.map_comp]
  change SheafOfModules.sectionsMap
    (((AlgebraicGeometry.Scheme.Modules.pullback r).map g.hom ≫
      (AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom) ≫ c.hom)
    (BundleSectionZeroLocus.pullbackSection r EW hr sw) =
    BundleSectionZeroLocus.pullbackSection (r ≫ h) EU hrh su
  calc
    SheafOfModules.sectionsMap
        (((AlgebraicGeometry.Scheme.Modules.pullback r).map g.hom ≫
          (AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom) ≫ c.hom)
        (BundleSectionZeroLocus.pullbackSection r EW hr sw) =
      SheafOfModules.sectionsMap c.hom
        (SheafOfModules.sectionsMap
          ((AlgebraicGeometry.Scheme.Modules.pullback r).map g.hom ≫
            (AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom)
          (BundleSectionZeroLocus.pullbackSection r EW hr sw)) :=
      SheafOfModules.sectionsMap_comp _ _ _
    _ = SheafOfModules.sectionsMap c.hom
        (SheafOfModules.sectionsMap
          ((AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom)
          (SheafOfModules.sectionsMap
            ((AlgebraicGeometry.Scheme.Modules.pullback r).map g.hom)
            (BundleSectionZeroLocus.pullbackSection r EW hr sw))) := by
      exact congrArg (SheafOfModules.sectionsMap c.hom)
        (SheafOfModules.sectionsMap_comp _ _ _)
    _ = SheafOfModules.sectionsMap c.hom
        (SheafOfModules.sectionsMap
          ((AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom)
          (BundleSectionZeroLocus.pullbackSection r
            ((AlgebraicGeometry.Scheme.Modules.restrictFunctor h).obj EU) hr sr)) := by
      exact congrArg (fun q => SheafOfModules.sectionsMap c.hom
        (SheafOfModules.sectionsMap
          ((AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom) q)) h1
    _ = SheafOfModules.sectionsMap c.hom
        (BundleSectionZeroLocus.pullbackSection r
          ((AlgebraicGeometry.Scheme.Modules.pullback h).obj EU) hr
          (BundleSectionZeroLocus.pullbackSection h EU hh su)) := by
      exact congrArg (SheafOfModules.sectionsMap c.hom) h2
    _ = BundleSectionZeroLocus.pullbackSection (r ≫ h) EU hrh su := h3


/-- The common overlap module is canonically the iterated pullback from the
right Serre trivialization. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToRightCompositeModuleIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLocalModule
      f C ij kl ≅
    (AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
        f C ij kl ≫ X.homOfLE
          (show C.U ij.1 ⊓ C.U kl.1 ≤ C.U kl.1 from inf_le_right))).obj
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
        (e.E.over (C.U kl.1))) := by
  let h' : (C.U ij.1 ⊓ C.U kl.1) ⟶ C.U kl.1 := homOfLE inf_le_right
  let h := X.homOfLE (leOfHom h')
  let r := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
    f C ij kl
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
    (e.E.over (C.U kl.1))
  let g := BundleSectionZeroLocus.localRestrictionTargetIso (E := e.E) h'
  change (AlgebraicGeometry.Scheme.Modules.pullback r).obj
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1 ⊓ C.U kl.1)).functor.obj
      (e.E.over (C.U ij.1 ⊓ C.U kl.1))) ≅
    (AlgebraicGeometry.Scheme.Modules.pullback (r ≫ h)).obj E
  exact
    (AlgebraicGeometry.Scheme.Modules.pullback r).mapIso
      (g ≪≫ (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback h).app E) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp r h).app E

/-- Transporting a common-overlap section to the iterated pullback from the
right Serre trivialization agrees with first restricting it to that chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection_toRightComposite
    (C : SerreExtensionRankTwoAffineCover e) (s : e.E.sections)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.sectionsMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToRightCompositeModuleIso
        f C ij kl).hom
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection
        f C s ij kl) =
    BundleSectionZeroLocus.pullbackSection
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
        f C ij kl ≫ X.homOfLE
          (show C.U ij.1 ⊓ C.U kl.1 ≤ C.U kl.1 from inf_le_right))
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
        (e.E.over (C.U kl.1)))
      (by
        rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_right]
        exact
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_pullbackUnitComparison_isIso
            f C ij kl)
      (BundleSectionZeroLocus.restrictSectionToOpen (C.U kl.1) s) := by
  let h' : (C.U ij.1 ⊓ C.U kl.1) ⟶ C.U kl.1 := homOfLE inf_le_right
  let h := X.homOfLE (leOfHom h')
  let r := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
    f C ij kl
  let EW := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1 ⊓ C.U kl.1)).functor.obj
    (e.E.over (C.U ij.1 ⊓ C.U kl.1))
  let EU := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
    (e.E.over (C.U kl.1))
  let g := BundleSectionZeroLocus.localRestrictionTargetIso (E := e.E) h'
  let a := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback h).app EU
  let c := (AlgebraicGeometry.Scheme.Modules.pullbackComp r h).app EU
  let sw := BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1 ⊓ C.U kl.1) s
  let su := BundleSectionZeroLocus.restrictSectionToOpen (C.U kl.1) s
  let sr := BundleSectionZeroLocus.restrictModuleSection h EU su
  haveI : IsOpenImmersion h := inferInstance
  have hr : IsIso (BundleSectionZeroLocus.pullbackUnitComparison r) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_pullbackUnitComparison_isIso
      f C ij kl
  have hh : IsIso (BundleSectionZeroLocus.pullbackUnitComparison h) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _ h.isOpenMap
  have hcomp : r ≫ h =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
        f C ij kl :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_right
      f C ij kl
  have hrh : IsIso (BundleSectionZeroLocus.pullbackUnitComparison (r ≫ h)) := by
    rw [hcomp]
    exact
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_pullbackUnitComparison_isIso
        f C ij kl
  have hg : SheafOfModules.sectionsMap g.hom sw = sr := by
    have hcompat := BundleSectionZeroLocus.localRestrictionTargetIso_sectionCompatibility h' s
    calc
      SheafOfModules.sectionsMap g.hom sw =
        SheafOfModules.sectionsMap g.hom (SheafOfModules.sectionsMap g.inv sr) := by
          exact congrArg (SheafOfModules.sectionsMap g.hom) hcompat.symm
      _ = sr := BundleSectionZeroLocus.sectionsMap_hom_inv g sr
  have h1 : SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullback r).map g.hom)
      (BundleSectionZeroLocus.pullbackSection r EW hr sw) =
      BundleSectionZeroLocus.pullbackSection r
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor h).obj EU) hr sr := by
    rw [BundleSectionZeroLocus.sectionsMap_pullbackSection]
    rw [hg]
  have h2 : SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom)
      (BundleSectionZeroLocus.pullbackSection r
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor h).obj EU) hr sr) =
      BundleSectionZeroLocus.pullbackSection r
        ((AlgebraicGeometry.Scheme.Modules.pullback h).obj EU) hr
        (BundleSectionZeroLocus.pullbackSection h EU hh su) := by
    refine (BundleSectionZeroLocus.sectionsMap_pullbackSection r a.hom hr sr).trans ?_
    exact congrArg (fun q => BundleSectionZeroLocus.pullbackSection r
      ((AlgebraicGeometry.Scheme.Modules.pullback h).obj EU) hr q)
      (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection h hh su)
  have h3 : SheafOfModules.sectionsMap c.hom
      (BundleSectionZeroLocus.pullbackSection r
        ((AlgebraicGeometry.Scheme.Modules.pullback h).obj EU) hr
        (BundleSectionZeroLocus.pullbackSection h EU hh su)) =
      BundleSectionZeroLocus.pullbackSection (r ≫ h) EU hrh su := by
    have hc := BundleSectionZeroLocus.pullbackSection_comp r h EU hr hh hrh su
    calc
      SheafOfModules.sectionsMap c.hom
          (BundleSectionZeroLocus.pullbackSection r
            ((AlgebraicGeometry.Scheme.Modules.pullback h).obj EU) hr
            (BundleSectionZeroLocus.pullbackSection h EU hh su)) =
        SheafOfModules.sectionsMap c.hom
          (SheafOfModules.sectionsMap c.inv
            (BundleSectionZeroLocus.pullbackSection (r ≫ h) EU hrh su)) := by
              exact congrArg (SheafOfModules.sectionsMap c.hom) hc.symm
      _ = BundleSectionZeroLocus.pullbackSection (r ≫ h) EU hrh su :=
        BundleSectionZeroLocus.sectionsMap_hom_inv c _
  dsimp [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToRightCompositeModuleIso,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLocalModule]
  rw [Functor.map_comp]
  change SheafOfModules.sectionsMap
    (((AlgebraicGeometry.Scheme.Modules.pullback r).map g.hom ≫
      (AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom) ≫ c.hom)
    (BundleSectionZeroLocus.pullbackSection r EW hr sw) =
    BundleSectionZeroLocus.pullbackSection (r ≫ h) EU hrh su
  calc
    SheafOfModules.sectionsMap
        (((AlgebraicGeometry.Scheme.Modules.pullback r).map g.hom ≫
          (AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom) ≫ c.hom)
        (BundleSectionZeroLocus.pullbackSection r EW hr sw) =
      SheafOfModules.sectionsMap c.hom
        (SheafOfModules.sectionsMap
          ((AlgebraicGeometry.Scheme.Modules.pullback r).map g.hom ≫
            (AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom)
          (BundleSectionZeroLocus.pullbackSection r EW hr sw)) :=
      SheafOfModules.sectionsMap_comp _ _ _
    _ = SheafOfModules.sectionsMap c.hom
        (SheafOfModules.sectionsMap
          ((AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom)
          (SheafOfModules.sectionsMap
            ((AlgebraicGeometry.Scheme.Modules.pullback r).map g.hom)
            (BundleSectionZeroLocus.pullbackSection r EW hr sw))) := by
      exact congrArg (SheafOfModules.sectionsMap c.hom)
        (SheafOfModules.sectionsMap_comp _ _ _)
    _ = SheafOfModules.sectionsMap c.hom
        (SheafOfModules.sectionsMap
          ((AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom)
          (BundleSectionZeroLocus.pullbackSection r
            ((AlgebraicGeometry.Scheme.Modules.restrictFunctor h).obj EU) hr sr)) := by
      exact congrArg (fun q => SheafOfModules.sectionsMap c.hom
        (SheafOfModules.sectionsMap
          ((AlgebraicGeometry.Scheme.Modules.pullback r).map a.hom) q)) h1
    _ = SheafOfModules.sectionsMap c.hom
        (BundleSectionZeroLocus.pullbackSection r
          ((AlgebraicGeometry.Scheme.Modules.pullback h).obj EU) hr
          (BundleSectionZeroLocus.pullbackSection h EU hh su)) := by
      exact congrArg (SheafOfModules.sectionsMap c.hom) h2
    _ = BundleSectionZeroLocus.pullbackSection (r ≫ h) EU hrh su := h3


/-- The intrinsic module on a product-chart overlap is canonically the left
local Serre presentation. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToLeftLocalModuleIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLocalModule
      f C ij kl ≅
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalModule
      f C ij kl :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToLeftCompositeModuleIso
    f C ij kl ≪≫
  (AlgebraicGeometry.Scheme.Modules.pullbackCongr
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_left
      f C ij kl)).app
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
      (e.E.over (C.U ij.1)))

/-- Under the left local presentation, the common-overlap restriction of any
global Serre section is its left-chart restriction. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection_toLeftLocal
    (C : SerreExtensionRankTwoAffineCover e) (s : e.E.sections)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.sectionsMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToLeftLocalModuleIso
        f C ij kl).hom
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection
        f C s ij kl) =
    BundleSectionZeroLocus.pullbackSection
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
        f C ij kl)
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
        (e.E.over (C.U ij.1)))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_pullbackUnitComparison_isIso
        f C ij kl)
      (BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1) s) := by
  let r := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
    f C ij kl
  let h := X.homOfLE (show C.U ij.1 ⊓ C.U kl.1 ≤ C.U ij.1 from inf_le_left)
  let p := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
    f C ij kl
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
    (e.E.over (C.U ij.1))
  let c := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToLeftCompositeModuleIso
    f C ij kl
  let pc := (AlgebraicGeometry.Scheme.Modules.pullbackCongr
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_left
      f C ij kl)).app E
  let sw := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection
    f C s ij kl
  let su := BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1) s
  have hcomp : r ≫ h = p :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_left
      f C ij kl
  have hrc : IsIso (BundleSectionZeroLocus.pullbackUnitComparison (r ≫ h)) := by
    rw [hcomp]
    exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_pullbackUnitComparison_isIso
      f C ij kl
  have hp : IsIso (BundleSectionZeroLocus.pullbackUnitComparison p) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_pullbackUnitComparison_isIso
      f C ij kl
  have hc : SheafOfModules.sectionsMap c.hom sw =
      BundleSectionZeroLocus.pullbackSection (r ≫ h) E hrc su := by
    exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection_toLeftComposite
      f C s ij kl
  change SheafOfModules.sectionsMap (c.hom ≫ pc.hom) sw =
    BundleSectionZeroLocus.pullbackSection p E hp su
  calc
    SheafOfModules.sectionsMap (c.hom ≫ pc.hom) sw =
      SheafOfModules.sectionsMap pc.hom (SheafOfModules.sectionsMap c.hom sw) :=
      SheafOfModules.sectionsMap_comp _ _ _
    _ = SheafOfModules.sectionsMap pc.hom
        (BundleSectionZeroLocus.pullbackSection (r ≫ h) E hrc su) := by rw [hc]
    _ = BundleSectionZeroLocus.pullbackSection p E hp su :=
      BundleSectionZeroLocus.sectionsMap_pullbackCongr_pullbackSection
        (r ≫ h) p hcomp E hrc hp su

/-- The intrinsic module on a product-chart overlap is canonically the right
local Serre presentation. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToRightLocalModuleIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLocalModule
      f C ij kl ≅
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalModule
      f C ij kl :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToRightCompositeModuleIso
    f C ij kl ≪≫
  (AlgebraicGeometry.Scheme.Modules.pullbackCongr
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_right
      f C ij kl)).app
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
      (e.E.over (C.U kl.1)))

/-- Under the right local presentation, the common-overlap restriction of any
global Serre section is its right-chart restriction. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection_toRightLocal
    (C : SerreExtensionRankTwoAffineCover e) (s : e.E.sections)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.sectionsMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToRightLocalModuleIso
        f C ij kl).hom
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection
        f C s ij kl) =
    BundleSectionZeroLocus.pullbackSection
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
        f C ij kl)
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
        (e.E.over (C.U kl.1)))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_pullbackUnitComparison_isIso
        f C ij kl)
      (BundleSectionZeroLocus.restrictSectionToOpen (C.U kl.1) s) := by
  let r := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap
    f C ij kl
  let h := X.homOfLE (show C.U ij.1 ⊓ C.U kl.1 ≤ C.U kl.1 from inf_le_right)
  let p := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
    f C ij kl
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
    (e.E.over (C.U kl.1))
  let c := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToRightCompositeModuleIso
    f C ij kl
  let pc := (AlgebraicGeometry.Scheme.Modules.pullbackCongr
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_right
      f C ij kl)).app E
  let sw := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection
    f C s ij kl
  let su := BundleSectionZeroLocus.restrictSectionToOpen (C.U kl.1) s
  have hcomp : r ≫ h = p :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToSerreOverlap_comp_right
      f C ij kl
  have hrc : IsIso (BundleSectionZeroLocus.pullbackUnitComparison (r ≫ h)) := by
    rw [hcomp]
    exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_pullbackUnitComparison_isIso
      f C ij kl
  have hp : IsIso (BundleSectionZeroLocus.pullbackUnitComparison p) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_pullbackUnitComparison_isIso
      f C ij kl
  have hc : SheafOfModules.sectionsMap c.hom sw =
      BundleSectionZeroLocus.pullbackSection (r ≫ h) E hrc su := by
    exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection_toRightComposite
      f C s ij kl
  change SheafOfModules.sectionsMap (c.hom ≫ pc.hom) sw =
    BundleSectionZeroLocus.pullbackSection p E hp su
  calc
    SheafOfModules.sectionsMap (c.hom ≫ pc.hom) sw =
      SheafOfModules.sectionsMap pc.hom (SheafOfModules.sectionsMap c.hom sw) :=
      SheafOfModules.sectionsMap_comp _ _ _
    _ = SheafOfModules.sectionsMap pc.hom
        (BundleSectionZeroLocus.pullbackSection (r ≫ h) E hrc su) := by rw [hc]
    _ = BundleSectionZeroLocus.pullbackSection p E hp su :=
      BundleSectionZeroLocus.sectionsMap_pullbackCongr_pullbackSection
        (r ≫ h) p hcomp E hrc hp su

/-- Pulling the selected rank-two presentation to a product chart gives an
explicit free rank-two presentation there. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.free
      (R := ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf)
      (ULift.{u} (Fin 2)) ≅
      SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij :=
  BundleSectionZeroLocus.pullbackFreeIsoOf_isOpenMap
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_isOpenMap f C ij)
    (ULift.{u} (Fin 2))
    (BundleSectionZeroLocus.localFreeIsoOfOver (C.U ij.1) (ULift.{u} (Fin 2))
      (C.trivialization ij.1))

/-- The chosen free presentation, transported through the local module
comparison, is a free presentation of the actual pullback of the global
Serre bundle on the parameter chart. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalGlobalFreeIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.free
      (R := ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf)
      (ULift.{u} (Fin 2)) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij ≫
          projectiveLineAmbientToScheme K f)).obj e.E :=
  SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij ≪≫
    SerreExtensionRankTwoAffineCover.projectiveLineLocalModuleIso f C ij

/-- The local unit comparison for a product chart is invertible. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij)) :=
  BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_isOpenMap f C ij)

noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftRestrictionToLocalModuleIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).obj
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) ≅
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalModule
      f C ij kl := by
  let p := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let q := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
    (e.E.over (C.U ij.1))
  exact ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback p).app
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp p q).app E)

theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftRestrictedPullbackSection_toLeftLocal
    (C : SerreExtensionRankTwoAffineCover e) (s₀ : e.E.sections)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.sectionsMap (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftRestrictionToLocalModuleIso f C ij kl).hom
      (BundleSectionZeroLocus.restrictModuleSection
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij)
        (BundleSectionZeroLocus.pullbackSection
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij)
          ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
            (e.E.over (C.U ij.1)))
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
            f C ij)
          (BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1) s₀))) =
    BundleSectionZeroLocus.pullbackSection
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme
        f C ij kl)
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
        (e.E.over (C.U ij.1)))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_pullbackUnitComparison_isIso
        f C ij kl)
      (BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1) s₀) := by
  let p := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let q := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
    (e.E.over (C.U ij.1))
  let a := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback p).app
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij)
  let c := (AlgebraicGeometry.Scheme.Modules.pullbackComp p q).app E
  let s := BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1) s₀
  let slocal := BundleSectionZeroLocus.pullbackSection q E
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
      f C ij) s
  haveI : IsOpenImmersion p :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_isOpenImmersion f C ij kl
  have hp : IsIso (BundleSectionZeroLocus.pullbackUnitComparison p) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_pullbackUnitComparison_isIso
      f C ij kl
  have hq : IsIso (BundleSectionZeroLocus.pullbackUnitComparison q) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
      f C ij
  have hpq : IsIso (BundleSectionZeroLocus.pullbackUnitComparison (p ≫ q)) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToLeftLocalScheme_pullbackUnitComparison_isIso
      f C ij kl
  have ha : SheafOfModules.sectionsMap a.hom
      (BundleSectionZeroLocus.restrictModuleSection p
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) slocal) =
      BundleSectionZeroLocus.pullbackSection p
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) hp slocal :=
    BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p hp slocal
  have hc : SheafOfModules.sectionsMap c.hom
      (BundleSectionZeroLocus.pullbackSection p
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) hp slocal) =
      BundleSectionZeroLocus.pullbackSection (p ≫ q) E hpq s := by
    have hcomp := BundleSectionZeroLocus.pullbackSection_comp p q E hp hq hpq s
    calc
      SheafOfModules.sectionsMap c.hom
          (BundleSectionZeroLocus.pullbackSection p
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) hp slocal) =
        SheafOfModules.sectionsMap c.hom
          (SheafOfModules.sectionsMap c.inv
            (BundleSectionZeroLocus.pullbackSection (p ≫ q) E hpq s)) := by
          exact congrArg (SheafOfModules.sectionsMap c.hom) hcomp.symm
      _ = BundleSectionZeroLocus.pullbackSection (p ≫ q) E hpq s :=
        BundleSectionZeroLocus.sectionsMap_hom_inv c _
  dsimp [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftRestrictionToLocalModuleIso]
  change SheafOfModules.sectionsMap (a.hom ≫ c.hom)
      (BundleSectionZeroLocus.restrictModuleSection p
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) slocal) =
    BundleSectionZeroLocus.pullbackSection (p ≫ q) E hpq s
  calc
    SheafOfModules.sectionsMap (a.hom ≫ c.hom)
        (BundleSectionZeroLocus.restrictModuleSection p
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) slocal) =
      SheafOfModules.sectionsMap c.hom
        (SheafOfModules.sectionsMap a.hom
          (BundleSectionZeroLocus.restrictModuleSection p
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) slocal)) :=
      SheafOfModules.sectionsMap_comp _ _ _
    _ = SheafOfModules.sectionsMap c.hom
        (BundleSectionZeroLocus.pullbackSection p
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) hp slocal) := by rw [ha]
    _ = BundleSectionZeroLocus.pullbackSection (p ≫ q) E hpq s := hc

noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightRestrictionToLocalModuleIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).obj
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) ≅
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalModule
      f C ij kl := by
  let p := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let q := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C kl
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
    (e.E.over (C.U kl.1))
  exact ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback p).app
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp p q).app E)

theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightRestrictedPullbackSection_toRightLocal
    (C : SerreExtensionRankTwoAffineCover e) (s₀ : e.E.sections)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.sectionsMap (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightRestrictionToLocalModuleIso f C ij kl).hom
      (BundleSectionZeroLocus.restrictModuleSection
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl)
        (BundleSectionZeroLocus.pullbackSection
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C kl)
          ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
            (e.E.over (C.U kl.1)))
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
            f C kl)
          (BundleSectionZeroLocus.restrictSectionToOpen (C.U kl.1) s₀))) =
    BundleSectionZeroLocus.pullbackSection
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme
        f C ij kl)
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
        (e.E.over (C.U kl.1)))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_pullbackUnitComparison_isIso
        f C ij kl)
      (BundleSectionZeroLocus.restrictSectionToOpen (C.U kl.1) s₀) := by
  let p := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let q := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C kl
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
    (e.E.over (C.U kl.1))
  let a := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback p).app
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl)
  let c := (AlgebraicGeometry.Scheme.Modules.pullbackComp p q).app E
  let s := BundleSectionZeroLocus.restrictSectionToOpen (C.U kl.1) s₀
  let slocal := BundleSectionZeroLocus.pullbackSection q E
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
      f C kl) s
  haveI : IsOpenImmersion p :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_snd_isOpenImmersion f C ij kl
  have hp : IsIso (BundleSectionZeroLocus.pullbackUnitComparison p) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_snd_pullbackUnitComparison_isIso
      f C ij kl
  have hq : IsIso (BundleSectionZeroLocus.pullbackUnitComparison q) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
      f C kl
  have hpq : IsIso (BundleSectionZeroLocus.pullbackUnitComparison (p ≫ q)) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapToRightLocalScheme_pullbackUnitComparison_isIso
      f C ij kl
  have ha : SheafOfModules.sectionsMap a.hom
      (BundleSectionZeroLocus.restrictModuleSection p
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) slocal) =
      BundleSectionZeroLocus.pullbackSection p
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) hp slocal :=
    BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p hp slocal
  have hc : SheafOfModules.sectionsMap c.hom
      (BundleSectionZeroLocus.pullbackSection p
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) hp slocal) =
      BundleSectionZeroLocus.pullbackSection (p ≫ q) E hpq s := by
    have hcomp := BundleSectionZeroLocus.pullbackSection_comp p q E hp hq hpq s
    calc
      SheafOfModules.sectionsMap c.hom
          (BundleSectionZeroLocus.pullbackSection p
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) hp slocal) =
        SheafOfModules.sectionsMap c.hom
          (SheafOfModules.sectionsMap c.inv
            (BundleSectionZeroLocus.pullbackSection (p ≫ q) E hpq s)) := by
          exact congrArg (SheafOfModules.sectionsMap c.hom) hcomp.symm
      _ = BundleSectionZeroLocus.pullbackSection (p ≫ q) E hpq s :=
        BundleSectionZeroLocus.sectionsMap_hom_inv c _
  dsimp [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightRestrictionToLocalModuleIso]
  change SheafOfModules.sectionsMap (a.hom ≫ c.hom)
      (BundleSectionZeroLocus.restrictModuleSection p
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) slocal) =
    BundleSectionZeroLocus.pullbackSection (p ≫ q) E hpq s
  calc
    SheafOfModules.sectionsMap (a.hom ≫ c.hom)
        (BundleSectionZeroLocus.restrictModuleSection p
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) slocal) =
      SheafOfModules.sectionsMap c.hom
        (SheafOfModules.sectionsMap a.hom
          (BundleSectionZeroLocus.restrictModuleSection p
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) slocal)) :=
      SheafOfModules.sectionsMap_comp _ _ _
    _ = SheafOfModules.sectionsMap c.hom
        (BundleSectionZeroLocus.pullbackSection p
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) hp slocal) := by rw [ha]
    _ = BundleSectionZeroLocus.pullbackSection (p ≫ q) E hpq s := hc

/-- The canonical Serre section restricted to an affine trivialization and
then pulled to its product chart. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij)
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
      (e.E.over (C.U ij.1)))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
      f C ij)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1) e.canonicalSection)

/-- The selected lift section restricted to an affine trivialization and then
pulled to its product chart. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij)
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
      (e.E.over (C.U ij.1)))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
      f C ij)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1) seed.lift)

/-- The rank-two bundle on the common intersection of two parameter charts,
pulled from their shared affine Serre trivialization. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModule
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :=
  (AlgebraicGeometry.Scheme.Modules.pullback
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme
      f C i b c)).obj
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
      (e.E.over (C.U i)))

/-- The module pulled from a common Serre trivialization to a chart overlap
is canonically the pullback of the original Serre bundle along the overlap
map to the surface. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModuleIso
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModule f C i b c ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToScheme
          f C i b c)).obj e.E := by
  let p := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme
    f C i b c
  let U := C.U i
  exact
    (AlgebraicGeometry.Scheme.Modules.pullback p).mapIso
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app e.E ≪≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app e.E) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp p U.ι).app e.E

/-- The common overlap retains an explicit free rank-two presentation. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalFreeIso
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SheafOfModules.free
      (R := (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
        f C i b c).ringCatSheaf)
      (ULift.{u} (Fin 2)) ≅
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModule
        f C i b c :=
  BundleSectionZeroLocus.pullbackFreeIsoOf_isOpenMap
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme
      f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme_isOpenMap
      f C i b c)
    (ULift.{u} (Fin 2))
    (BundleSectionZeroLocus.localFreeIsoOfOver (C.U i) (ULift.{u} (Fin 2))
      (C.trivialization i))

/-- The overlap free presentation, transported to the pullback of the
global Serre bundle. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalGlobalFreeIso
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SheafOfModules.free
      (R := (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
        f C i b c).ringCatSheaf)
      (ULift.{u} (Fin 2)) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToScheme
          f C i b c)).obj e.E :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalFreeIso f C i b c ≪≫
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModuleIso f C i b c

/-- Pullback of the unit module is invertible on the common parameter-chart
intersection. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme_pullbackUnitComparison_isIso
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme
        f C i b c)) :=
  BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme_isOpenMap
      f C i b c)

/-- The canonical Serre generator on a parameter-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalCanonicalSection
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModule
      f C i b c).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme
      f C i b c)
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
      (e.E.over (C.U i)))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme_pullbackUnitComparison_isIso
      f C i b c)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U i) e.canonicalSection)

/-- The selected lifted Serre generator on a parameter-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalLiftSection
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) (b c : Bool) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModule
      f C i b c).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme
      f C i b c)
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
      (e.E.over (C.U i)))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme_pullbackUnitComparison_isIso
      f C i b c)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U i) seed.lift)

/-- The canonical generator expressed through the right chart map.  This is
definitionally indexed by the right composite, so it can be compared with a
pullback from that chart without dependent transports. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalCanonicalSection
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme
        f C i b c)).obj
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
        (e.E.over (C.U i)))).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme
      f C i b c)
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
      (e.E.over (C.U i)))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_pullbackUnitComparison_isIso
      f C i b c)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U i) e.canonicalSection)

/-- The selected lifted generator expressed through the right chart map. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalLiftSection
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) (b c : Bool) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme
        f C i b c)).obj
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
        (e.E.over (C.U i)))).sections :=
  BundleSectionZeroLocus.pullbackSection
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme
      f C i b c)
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
      (e.E.over (C.U i)))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_pullbackUnitComparison_isIso
      f C i b c)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U i) seed.lift)

/-- Transporting the right-indexed canonical generator along equality of the
two maps to the Serre trivialization gives the shared overlap generator. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalCanonicalSection_eq
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_eq
          f C i b c)).hom.app
        ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
          (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalCanonicalSection
        f C i b c) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalCanonicalSection
        f C i b c :=
  BundleSectionZeroLocus.sectionsMap_pullbackCongr_pullbackSection _ _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_eq f C i b c)
    _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_pullbackUnitComparison_isIso
      f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme_pullbackUnitComparison_isIso
      f C i b c)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U i) e.canonicalSection)

/-- The same transport identifies the selected lift from the right chart
with the shared overlap lift. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalLiftSection_eq
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) (b c : Bool) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_eq
          f C i b c)).hom.app
        ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
          (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalLiftSection
        f C seed i b c) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalLiftSection
        f C seed i b c :=
  BundleSectionZeroLocus.sectionsMap_pullbackCongr_pullbackSection _ _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_eq f C i b c)
    _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_pullbackUnitComparison_isIso
      f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme_pullbackUnitComparison_isIso
      f C i b c)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U i) seed.lift)

/-- On an intersection of parameter charts, the canonical Serre generator
is the pullback of the generator from the left chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalCanonicalSection_pullback_fst
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, b))).inv.app
          ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
            (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalCanonicalSection
        f C i b c) =
    BundleSectionZeroLocus.pullbackSection
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, b))).obj
        ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
          (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_fst_pullbackUnitComparison_isIso
        f C i b c)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C (i, b)) := by
  exact BundleSectionZeroLocus.pullbackSection_comp _ _ _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_fst_pullbackUnitComparison_isIso
      f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
      f C (i, b))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme_pullbackUnitComparison_isIso
      f C i b c)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U i) e.canonicalSection)

/-- On an intersection of parameter charts, the lifted Serre generator is
the pullback of the generator from the left chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalLiftSection_pullback_fst
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) (b c : Bool) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, b))).inv.app
          ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
            (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalLiftSection
        f C seed i b c) =
    BundleSectionZeroLocus.pullbackSection
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, b))).obj
        ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
          (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_fst_pullbackUnitComparison_isIso
        f C i b c)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed (i, b)) := by
  exact BundleSectionZeroLocus.pullbackSection_comp _ _ _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_fst_pullbackUnitComparison_isIso
      f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
      f C (i, b))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToLocalScheme_pullbackUnitComparison_isIso
      f C i b c)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U i) seed.lift)

/-- The right-indexed canonical overlap generator is the pullback of the
canonical generator from the right parameter chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalCanonicalSection_pullback_snd
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c))).inv.app
          ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
            (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalCanonicalSection
        f C i b c) =
    BundleSectionZeroLocus.pullbackSection
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c))).obj
        ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
          (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
        f C i b c)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C (i, c)) := by
  exact BundleSectionZeroLocus.pullbackSection_comp _ _ _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
      f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
      f C (i, c))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_pullbackUnitComparison_isIso
      f C i b c)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U i) e.canonicalSection)

/-- The right-indexed lifted overlap generator is the pullback of the
selected lift from the right parameter chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalLiftSection_pullback_snd
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) (b c : Bool) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c))).inv.app
          ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
            (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalLiftSection
        f C seed i b c) =
    BundleSectionZeroLocus.pullbackSection
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c))).obj
        ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
          (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
        f C i b c)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed (i, c)) := by
  exact BundleSectionZeroLocus.pullbackSection_comp _ _ _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
      f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme_pullbackUnitComparison_isIso
      f C (i, c))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_pullbackUnitComparison_isIso
      f C i b c)
    (BundleSectionZeroLocus.restrictSectionToOpen (C.U i) seed.lift)

/-- A local member of the Serre pencil on a product chart.  The coefficients
are regular functions on the affine parameter chart, represented as
endomorphisms of its unit module. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (a b : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij).sections :=
  BundleSectionZeroLocus.addSections
    (BundleSectionZeroLocus.scaleSection a
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C ij))
    (BundleSectionZeroLocus.scaleSection b
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed ij))

/- The named scalar coordinates of a local pencil member are the ordinary
   linear combination of the coordinates of the canonical and lifted
   sections.  This is the coordinate-level form of the pencil equation; it
   makes later Jacobian or unit arguments independent of the sheaf-level
   `addSections`/`scaleSection` construction. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf_coordinate
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (a b : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf)
    (i : ULift.{u} (Fin 2)) :
    BundleSectionZeroLocus.sectionCoordinateOfFreeIso
        (ULift.{u} (Fin 2))
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
          f C seed ij a b) i =
      BundleSectionZeroLocus.unitEndomorphismValue a *
        BundleSectionZeroLocus.sectionCoordinateOfFreeIso
          (ULift.{u} (Fin 2))
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection
            f C ij) i +
      BundleSectionZeroLocus.unitEndomorphismValue b *
        BundleSectionZeroLocus.sectionCoordinateOfFreeIso
          (ULift.{u} (Fin 2))
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection
            f C seed ij) i := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
  rw [BundleSectionZeroLocus.sectionCoordinateOfFreeIso_add,
    BundleSectionZeroLocus.sectionCoordinateOfFreeIso_scale,
    BundleSectionZeroLocus.sectionCoordinateOfFreeIso_scale]

/-- Pulling a local pencil equation from the right parameter chart to an
overlap pulls back both coefficients through the canonical unit comparison.
This is the coefficient-level restriction formula used before applying the
projective transition scalar. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf_pullback_snd
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool)
    (a d : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)).ringCatSheaf) :
    BundleSectionZeroLocus.pullbackSection
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
        f C i b c)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
        f C seed (i, c) a d) =
    BundleSectionZeroLocus.addSections
      (BundleSectionZeroLocus.scaleSection
        (BundleSectionZeroLocus.pullbackUnitEndomorphism
          (pullback.snd
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
            f C i b c) a)
        (BundleSectionZeroLocus.pullbackSection
          (pullback.snd
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c))
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
            f C i b c)
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C (i, c))))
      (BundleSectionZeroLocus.scaleSection
        (BundleSectionZeroLocus.pullbackUnitEndomorphism
          (pullback.snd
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
            f C i b c) d)
        (BundleSectionZeroLocus.pullbackSection
          (pullback.snd
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c))
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
            f C i b c)
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed (i, c)))) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
  exact BundleSectionZeroLocus.pullbackSection_linearCombination _ _ a d _ _

/-- The right-chart pencil equation, expressed directly on the overlap.
Its coefficients are the canonical pullbacks of the chart coefficients. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool)
    (a d : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)).ringCatSheaf) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme
        f C i b c)).obj
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
        (e.E.over (C.U i)))).sections :=
  BundleSectionZeroLocus.addSections
    (BundleSectionZeroLocus.scaleSection
      (BundleSectionZeroLocus.pullbackUnitEndomorphism
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
          f C i b c) a)
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalCanonicalSection
        f C i b c))
    (BundleSectionZeroLocus.scaleSection
      (BundleSectionZeroLocus.pullbackUnitEndomorphism
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
          f C i b c) d)
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalLiftSection
        f C seed i b c))

/-- Transporting the direct right-overlap pencil equation through pullback
composition recovers the pullback of the original right-chart equation. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf_pullback_snd
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool)
    (a d : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)).ringCatSheaf) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c))).inv.app
          ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
            (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf
        f C seed i b c a d) =
    BundleSectionZeroLocus.pullbackSection
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
        f C i b c)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
        f C seed (i, c) a d) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf
  rw [BundleSectionZeroLocus.sectionsMap_addSections,
    BundleSectionZeroLocus.sectionsMap_scaleSection,
    BundleSectionZeroLocus.sectionsMap_scaleSection,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalCanonicalSection_pullback_snd,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalLiftSection_pullback_snd,
    ← SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf_pullback_snd]

/-- Reversing the pullback-composition presentation of a right-chart pencil
section recovers its direct overlap presentation. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf_pullback_snd_hom
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool)
    (a d : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)).ringCatSheaf) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c))).hom.app
          ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
            (e.E.over (C.U i))))
      (BundleSectionZeroLocus.pullbackSection
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c))
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
          f C i b c)
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
          f C seed (i, c) a d)) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf
        f C seed i b c a d := by
  let p := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))
  let q := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c)
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
    (e.E.over (C.U i))
  let B := (AlgebraicGeometry.Scheme.Modules.pullbackComp p q).app E
  let s := SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
    f C seed (i, c) a d
  let t := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf
    f C seed i b c a d
  have hraw := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf_pullback_snd
    f C seed i b c a d
  exact (congrArg (SheafOfModules.sectionsMap B.hom) hraw.symm).trans
    (BundleSectionZeroLocus.sectionsMap_hom_inv B t)

/-- The coordinate ideal of a local parameter-pencil member, computed using
the pulled-back rank-two trivialization. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilZeroIdealOf
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (a b : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf) :
    AlgebraicGeometry.Scheme.IdealSheafData
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf f C seed ij a b)

/-- The free presentation induced by restricting the right product chart to
an overlap. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightRestrictedFreeIso
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    SheafOfModules.free
      (R := (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
        f C i b c).ringCatSheaf)
      (ULift.{u} (Fin 2)) ≅
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))).obj
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c)) :=
  BundleSectionZeroLocus.restrictionFreeIsoOf _ (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C (i, c))

/-- The right local pencil equation after canonical restriction to an
overlap of parameter charts. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightRestrictedPencilSection
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool)
    (a d : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)).ringCatSheaf) :
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))).obj
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c))).sections :=
  BundleSectionZeroLocus.restrictModuleSection _
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c))
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf f C seed (i, c) a d)

/-- The restricted right-chart module is canonically the common module on
the overlap.  The comparison factors through restriction-versus-pullback,
pullback composition, and the equality of the two maps to the shared Serre
trivialization. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightRestrictionToSharedModuleIso
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))).obj
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c)) ≅
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModule
        f C i b c := by
  let p := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))
  let q := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c)
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
    (e.E.over (C.U i))
  exact ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback p).app
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c)) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp p q).app E ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_eq
        f C i b c)).app E)

/-- Restricting a local pencil zero ideal to an affine parameter-chart
intersection is computed by the canonically restricted free presentation
and equation. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilZeroIdealOf_comap_snd
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool)
    (a d : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)).ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilZeroIdealOf
      f C seed (i, c) a d).comap
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))) =
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2))
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightRestrictedFreeIso
          f C i b c)
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightRestrictedPencilSection
          f C seed i b c a d) := by
  let p := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))
  letI : IsAffine
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_affine f C i b c
  letI : IsAffine ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X (i, c)) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_affine f C (i, c)
  exact BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction
    p (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C (i, c))
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf f C seed (i, c) a d)

/-- Rescaling both homogeneous coefficients rescales the local pencil
section by the same scalar.  This is the algebraic compatibility needed on
the intersection of the two standard projective-line charts. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf_commonScale
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (u a b : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf) :
    BundleSectionZeroLocus.scaleSection u
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf f C seed ij a b) =
      SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf f C seed ij
        (u ≫ a) (u ≫ b) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
  rw [BundleSectionZeroLocus.scaleSection_addSections,
    BundleSectionZeroLocus.scaleSection_scaleSection,
    BundleSectionZeroLocus.scaleSection_scaleSection]

/-- An invertible common rescaling of the homogeneous coefficients leaves the
local pencil zero ideal unchanged. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilZeroIdealOf_commonScale
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (u a b : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf)
    [IsIso u] :
    SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilZeroIdealOf f C seed ij a b =
      SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilZeroIdealOf f C seed ij
        (u ≫ a) (u ≫ b) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilZeroIdealOf
  rw [← SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf_commonScale
    f C seed ij u a b]
  exact (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso
    (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij) u _).symm

/-- A Serre-pencil member formed directly on the common intersection of two
parameter charts. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilSectionOf
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool)
    (a d : SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
        f C i b c).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
          f C i b c).ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModule
      f C i b c).sections :=
  BundleSectionZeroLocus.addSections
    (BundleSectionZeroLocus.scaleSection a
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalCanonicalSection
        f C i b c))
    (BundleSectionZeroLocus.scaleSection d
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalLiftSection
        f C seed i b c))

/-- The coordinate ideal of an overlap pencil member in the shared free
rank-two presentation. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilZeroIdealOf
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool)
    (a d : SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
        f C i b c).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
          f C i b c).ringCatSheaf) :
    AlgebraicGeometry.Scheme.IdealSheafData
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
        f C i b c) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalFreeIso
      f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilSectionOf
      f C seed i b c a d)

/-- Common rescaling of the two homogeneous coefficients rescales the
intersection pencil section itself. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilSectionOf_commonScale
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool)
    (u a d : SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
        f C i b c).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
          f C i b c).ringCatSheaf) :
    BundleSectionZeroLocus.scaleSection u
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilSectionOf
        f C seed i b c a d) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilSectionOf
        f C seed i b c (u ≫ a) (u ≫ d) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilSectionOf
  rw [BundleSectionZeroLocus.scaleSection_addSections,
    BundleSectionZeroLocus.scaleSection_scaleSection,
    BundleSectionZeroLocus.scaleSection_scaleSection]

/-- The overlap pencil ideals agree after an invertible common rescaling. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilZeroIdealOf_commonScale
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool)
    (u a d : SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
        f C i b c).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap
          f C i b c).ringCatSheaf)
    [IsIso u] :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilZeroIdealOf
      f C seed i b c a d =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilZeroIdealOf
        f C seed i b c (u ≫ a) (u ≫ d) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilZeroIdealOf
  rw [← SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilSectionOf_commonScale
    f C seed i b c u a d]
  exact (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso
    (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalFreeIso
      f C i b c) u _).symm

/-- The normalized pencil section from the left projective-line chart, formed
on the actual chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilSection
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilSectionOf
    f C seed i b c
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftCoefficients
      f C i b c).1
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftCoefficients
      f C i b c).2

/-- The normalized pencil section from the right projective-line chart,
formed on the actual chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilSection
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModule
      f C i b c).sections :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilSectionOf
    f C seed i b c
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
      f C i b c).1
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
      f C i b c).2

/-- On the nontrivial parameter-chart overlap, the two normalized pencil
sections are related by the invertible projective transition scalar. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedPencilSection_commonScale
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool)
    (hbc : b ≠ c) :
    BundleSectionZeroLocus.scaleSection
      (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit f C i b c))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilSection
        f C seed i b c) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilSection
        f C seed i b c := by
  unfold
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilSection
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilSection
  rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedCoefficients_commonScale
    f C i b c hbc]
  exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilSectionOf_commonScale
    f C seed i b c _ _ _

/-- The zero ideal of the normalized equation written in the left
projective-line chart, on a parameter-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdeal
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    AlgebraicGeometry.Scheme.IdealSheafData
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c) :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilZeroIdealOf
    f C seed i b c
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftCoefficients
      f C i b c).1
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftCoefficients
      f C i b c).2

/-- The zero ideal of the normalized equation written in the right
projective-line chart, on a parameter-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdeal
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    AlgebraicGeometry.Scheme.IdealSheafData
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c) :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilZeroIdealOf
    f C seed i b c
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
      f C i b c).1
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
      f C i b c).2

/-- The left normalized overlap section, transported to the actual pullback
of the global Serre bundle. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilSectionOnGlobalBundle
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToScheme
        f C i b c)).obj e.E).sections :=
  SheafOfModules.sectionsMap
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModuleIso
      f C i b c).hom
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilSection
      f C seed i b c)

/-- The right normalized overlap section, transported to the actual pullback
of the global Serre bundle. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilSectionOnGlobalBundle
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToScheme
        f C i b c)).obj e.E).sections :=
  SheafOfModules.sectionsMap
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModuleIso
      f C i b c).hom
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilSection
      f C seed i b c)

/-- The left normalized overlap zero ideal, calculated in a free
presentation of the pulled-back global bundle. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdealOnGlobalBundle
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    AlgebraicGeometry.Scheme.IdealSheafData
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalGlobalFreeIso
      f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilSectionOnGlobalBundle
      f C seed i b c)

/-- The right normalized overlap zero ideal, calculated in a free
presentation of the pulled-back global bundle. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdealOnGlobalBundle
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    AlgebraicGeometry.Scheme.IdealSheafData
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap f C i b c) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalGlobalFreeIso
      f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilSectionOnGlobalBundle
      f C seed i b c)

/-- Transporting the left overlap section to the global bundle preserves its
coordinate zero ideal. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdeal_eq_onGlobalBundle
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdeal
      f C seed i b c =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdealOnGlobalBundle
        f C seed i b c := by
  exact BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq
    (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalFreeIso f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModuleIso f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilSection
      f C seed i b c)

/-- Transporting the right overlap section to the global bundle preserves its
coordinate zero ideal. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdeal_eq_onGlobalBundle
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdeal
      f C seed i b c =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdealOnGlobalBundle
        f C seed i b c := by
  exact BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq
    (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalFreeIso f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalModuleIso f C i b c)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilSection
      f C seed i b c)

/-- The overlap zero ideals of the two normalized parameter-chart equations
are literally equal in their shared free rank-two presentation. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedPencilZeroIdeal_eq
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool)
    (hbc : b ≠ c) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdeal
      f C seed i b c =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdeal
        f C seed i b c := by
  unfold
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdeal
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdeal
  let u := BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapUnit f C i b c)
  letI : IsIso u :=
    SerreExtensionRankTwoAffineCover.isIso_projectiveLineOpenCoverOverlapUnitCoefficient
      f C i b c
  rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedCoefficients_commonScale
    f C i b c hbc]
  exact (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilZeroIdealOf_commonScale
    f C seed i b c u _ _).symm

/-- On a self-overlap, the two normalized local equations are identical
before applying any transition rescaling. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedPencilZeroIdeal_eq_of_eq
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdeal
      f C seed i b b =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdeal
        f C seed i b b := by
  unfold
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdeal
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdeal
  rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedCoefficients_eq_of_eq
    f C i b]

/-- The normalized local zero ideals agree on every overlap of the two
standard projective-line charts, including a self-overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedPencilZeroIdeal_eq_all
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdeal
      f C seed i b c =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdeal
        f C seed i b c := by
  by_cases hbc : b = c
  · subst c
    exact
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedPencilZeroIdeal_eq_of_eq
        f C seed i b
  · exact
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedPencilZeroIdeal_eq
        f C seed i b c hbc

/-- On every overlap of the two standard parameter charts, the normalized
equations define the same zero ideal after both are expressed in the actual
pullback of the global Serre bundle. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedPencilZeroIdeal_eq_all_onGlobalBundle
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdealOnGlobalBundle
      f C seed i b c =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdealOnGlobalBundle
        f C seed i b c := by
  rw [← SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdeal_eq_onGlobalBundle,
    ← SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdeal_eq_onGlobalBundle]
  exact
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedPencilZeroIdeal_eq_all
      f C seed i b c

/-- The equality of normalized overlap ideals yields the explicit transition
isomorphism between their closed zero subschemes. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedPencilZeroSubschemeTransition
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdeal
      f C seed i b c).subscheme ≅
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdeal
        f C seed i b c).subscheme :=
  eqToIso (congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedPencilZeroIdeal_eq_all
      f C seed i b c))

/-- The overlap transition is over the common ambient overlap chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedPencilZeroSubschemeTransition_hom_comp_subschemeι
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedPencilZeroSubschemeTransition
      f C seed i b c).hom ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilZeroIdeal
        f C seed i b c).subschemeι =
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedLeftPencilZeroIdeal
        f C seed i b c).subschemeι := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedPencilZeroSubschemeTransition
  exact idealSheafData_eqToIso_subschemeι _ _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_normalizedPencilZeroIdeal_eq_all
      f C seed i b c)

/-- The corresponding local closed subscheme of a parameter-pencil member. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilZeroSubschemeOf
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (a b : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf) :
    Scheme.{u} :=
  (SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilZeroIdealOf
    f C seed ij a b).subscheme

/-- The ordinary affine slope coordinate on a product chart.  It is pulled
back from the corresponding standard chart of the projective line. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinate
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤) :=
  affineFunctionHom
    (pullback.snd ((C.U ij.1).ι ≫ f)
      ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K))
    (chartCoordinate I₀ ij.2 (!ij.2))

/-- The slope coordinate as a scalar endomorphism of the unit module on its
product chart. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf :=
  BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinate f C ij)

/-- The scalar recorded by the coordinate endomorphism is the ordinary
affine slope function. -/
theorem SerreExtensionRankTwoAffineCover.unitEndomorphismValue_projectiveLineLocalCoordinateCoefficient
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    BundleSectionZeroLocus.unitEndomorphismValue
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij) =
      SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinate f C ij :=
  BundleSectionZeroLocus.unitEndomorphismValue_ofRegularFunction
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinate f C ij)

/-- Restricting the nonconstant normalized coordinate from the right parameter
chart gives the corresponding coordinate endomorphism on the intersection. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_pullback_rightCoordinateCoefficient
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    BundleSectionZeroLocus.pullbackUnitEndomorphism
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
        f C i b c)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C (i, c)) =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
      f C i b c (!c) := by
  let p := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))
  letI : IsOpenImmersion p :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_isOpenImmersion
      f C i b c
  unfold SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightCoordinateCoefficient
  rw [BundleSectionZeroLocus.pullbackUnitEndomorphismOfRegularFunction_eq_appTop]
  congr 1

/-- The normalized homogeneous coefficient pair on a standard
projective-line chart: the distinguished coordinate is one and the other is
the affine slope. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf) ×
    (SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf) :=
  by
  classical
  exact if ij.2 = true then
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij, 𝟙 _)
  else
    (𝟙 _, SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij)

/-- On the chart indexed by true, the normalized pencil equation has the
affine slope multiplying the canonical section and coefficient one on the
chosen lift. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients_of_eq_true
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 = true) :
    SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C ij =
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij, 𝟙 _) := by
  classical
  unfold SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients
  rw [if_pos hij]

/-- On the chart indexed by false, the normalized pencil equation has
coefficient one on the canonical section and affine slope on the lift. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients_of_eq_false
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 = false) :
    SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C ij =
      (𝟙 _, SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij) := by
  classical
  unfold SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients
  rw [if_neg (by simpa [hij])]

/-- The normalized coefficient pair from the right chart pulls back to the
normalized right coefficient pair on a parameter-chart intersection. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_pullback_normalizedRightCoefficients
    (C : SerreExtensionRankTwoAffineCover e) (i : C.ι) (b c : Bool) :
    (BundleSectionZeroLocus.pullbackUnitEndomorphism
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
        f C i b c)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).1,
     BundleSectionZeroLocus.pullbackUnitEndomorphism
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
        f C i b c)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).2) =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
      f C i b c := by
  cases c
  · rw [SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients_of_eq_false
      f C (i, false) rfl]
    unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
    rw [if_neg (by decide)]
    change (_, _) = (_, _)
    rw [BundleSectionZeroLocus.pullbackUnitEndomorphism_id,
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_pullback_rightCoordinateCoefficient]
  · rw [SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients_of_eq_true
      f C (i, true) rfl]
    unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
    rw [if_pos rfl]
    change (_, _) = (_, _)
    rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_pullback_rightCoordinateCoefficient,
      BundleSectionZeroLocus.pullbackUnitEndomorphism_id]

/-- The normalized right equation written with the right presentation of the
overlap-to-trivialization map. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightNormalizedLocalPencilSection
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme
        f C i b c)).obj
      ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
        (e.E.over (C.U i)))).sections :=
  BundleSectionZeroLocus.addSections
    (BundleSectionZeroLocus.scaleSection
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
        f C i b c).1
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalCanonicalSection
        f C i b c))
    (BundleSectionZeroLocus.scaleSection
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
        f C i b c).2
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalLiftSection
        f C seed i b c))

/-- The direct pullback of the normalized right chart equation is exactly the
right-presented normalized overlap equation. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf_normalized
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf
      f C seed i b c
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).1
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).2 =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightNormalizedLocalPencilSection
      f C seed i b c := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightNormalizedLocalPencilSection
  have h := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_pullback_normalizedRightCoefficients
    f C i b c
  have h₁ : BundleSectionZeroLocus.pullbackUnitEndomorphism
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
        f C i b c)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).1 =
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
      f C i b c).1 := by
    exact congrArg Prod.fst h
  have h₂ : BundleSectionZeroLocus.pullbackUnitEndomorphism
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
        f C i b c)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).2 =
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightCoefficients
      f C i b c).2 := by
    exact congrArg Prod.snd h
  rw [h₁, h₂]

/-- Transporting the right-presented normalized equation to the common
overlap-to-trivialization map recovers the shared normalized right equation. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightNormalizedLocalPencilSection_eq
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_eq
          f C i b c)).hom.app
        ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
          (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightNormalizedLocalPencilSection
        f C seed i b c) =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilSection
      f C seed i b c := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightNormalizedLocalPencilSection
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilSection
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapLocalPencilSectionOf
  rw [BundleSectionZeroLocus.sectionsMap_addSections,
    BundleSectionZeroLocus.sectionsMap_scaleSection,
    BundleSectionZeroLocus.sectionsMap_scaleSection,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalCanonicalSection_eq,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalLiftSection_eq]

/-- The normalized right chart equation, pulled first to the right overlap
presentation and then transported to the common presentation, is the shared
normalized right overlap equation. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf_normalized_eq
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapToRightLocalScheme_eq
          f C i b c)).hom.app
        ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
          (e.E.over (C.U i))))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf
        f C seed i b c
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).1
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).2) =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapNormalizedRightPencilSection
      f C seed i b c := by
  rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf_normalized]
  exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightNormalizedLocalPencilSection_eq
    f C seed i b c

/-- Restricting a normalized right-chart equation and then forming the
pullback composite recovers its direct right-overlap equation. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightRestrictedNormalizedSection_to_right
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (i : C.ι) (b c : Bool) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c))).hom.app
          ((AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
            (e.E.over (C.U i))))
      (SheafOfModules.sectionsMap
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback
          (pullback.snd
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c)))).hom.app
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c)))
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightRestrictedPencilSection
          f C seed i b c
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).1
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).2)) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf
        f C seed i b c
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).1
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).2 := by
  let p := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))
  let q := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C (i, c)
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U i)).functor.obj
    (e.E.over (C.U i))
  let A := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback p).app
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c))
  let B := (AlgebraicGeometry.Scheme.Modules.pullbackComp p q).app E
  let s := SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
    f C seed (i, c)
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).1
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).2
  change SheafOfModules.sectionsMap B.hom
    (SheafOfModules.sectionsMap A.hom
      (BundleSectionZeroLocus.restrictModuleSection p
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c)) s)) = _
  refine (congrArg (SheafOfModules.sectionsMap B.hom)
    (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p
      (E := SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C (i, c))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlap_snd_pullbackUnitComparison_isIso
        f C i b c) s)).trans ?_
  exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverOverlapRightLocalPencilSectionOf_pullback_snd_hom
    f C seed i b c
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).1
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C (i, c)).2

/-- The Serre-pencil section with the actual normalized projective-line
coefficients on its affine parameter chart. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij).sections :=
  SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf f C seed ij
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C ij).1
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C ij).2

/-- The normalized local section has its expected slope--lift form on the
true parameter chart. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection_of_eq_true
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 = true) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection f C seed ij =
      SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf f C seed ij
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij) (𝟙 _) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection
  rw [SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients_of_eq_true
    f C ij hij]

/-- The normalized local section has its expected canonical--slope form on
the false parameter chart. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection_of_eq_false
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 = false) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection f C seed ij =
      SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf f C seed ij
        (𝟙 _) (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection
  rw [SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients_of_eq_false
    f C ij hij]

/- On the true parameter chart, the first coefficient is the local slope and
   the second coefficient is the unit.  This exposes the corresponding
   ordinary ring-function formula for every named section coordinate. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinate_of_eq_true
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 = true)
    (i : ULift.{u} (Fin 2)) :
    BundleSectionZeroLocus.sectionCoordinateOfFreeIso
        (ULift.{u} (Fin 2))
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection
          f C seed ij) i =
      BundleSectionZeroLocus.unitEndomorphismValue
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij) *
        BundleSectionZeroLocus.sectionCoordinateOfFreeIso
          (ULift.{u} (Fin 2))
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C ij) i +
      BundleSectionZeroLocus.unitEndomorphismValue (𝟙 _) *
        BundleSectionZeroLocus.sectionCoordinateOfFreeIso
          (ULift.{u} (Fin 2))
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed ij) i := by
  rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection_of_eq_true
    f C seed ij hij]
  exact SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf_coordinate
    f C seed ij (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij)
    (𝟙 _) i

/- On the false parameter chart, the first coefficient is the unit and the
   second coefficient is the local slope. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinate_of_eq_false
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 = false)
    (i : ULift.{u} (Fin 2)) :
    BundleSectionZeroLocus.sectionCoordinateOfFreeIso
        (ULift.{u} (Fin 2))
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection
          f C seed ij) i =
      BundleSectionZeroLocus.unitEndomorphismValue (𝟙 _) *
        BundleSectionZeroLocus.sectionCoordinateOfFreeIso
          (ULift.{u} (Fin 2))
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C ij) i +
      BundleSectionZeroLocus.unitEndomorphismValue
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij) *
        BundleSectionZeroLocus.sectionCoordinateOfFreeIso
          (ULift.{u} (Fin 2))
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed ij) i := by
  rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection_of_eq_false
    f C seed ij hij]
  exact SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf_coordinate
    f C seed ij (𝟙 _)
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij) i

/-- The local zero ideal of the actual normalized parameter-pencil member. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    AlgebraicGeometry.Scheme.IdealSheafData
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij) :=
  SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilZeroIdealOf f C seed ij
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C ij).1
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C ij).2

/-- On every affine product chart, the normalized rank-two pencil zero ideal
is the ideal generated by its two free-section coordinates. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_eq_twoCoordinates
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal f C seed ij =
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        (Ideal.span
          {BundleSectionZeroLocus.sectionCoordinateOfFreeIso
            (ULift.{u} (Fin 2))
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
            (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection
              f C seed ij) (ULift.up 0)} ⊔
          Ideal.span
            {BundleSectionZeroLocus.sectionCoordinateOfFreeIso
              (ULift.{u} (Fin 2))
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
              (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection
                f C seed ij) (ULift.up 1)}) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
  change BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection f C seed ij) = _
  exact BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_ulift_fin_two_eq _ _

/-- The ordered pair of scalar coordinates of the actual normalized
rank-two pencil section on a product chart. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤) ×
      Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤) :=
  (BundleSectionZeroLocus.sectionCoordinateOfFreeIso
    (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection
      f C seed ij) (ULift.up 0),
  BundleSectionZeroLocus.sectionCoordinateOfFreeIso
    (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection
      f C seed ij) (ULift.up 1))

/-- The local zero ideal of the actual normalized pencil is the ideal of its
ordered coordinate pair. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_eq_coordinates
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal f C seed ij =
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        (Ideal.span
          {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
            f C seed ij).1} ⊔
          Ideal.span
          {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
            f C seed ij).2}) := by
  exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_eq_twoCoordinates
    f C seed ij

/-- The actual normalized local zero chart is the affine spectrum of the
quotient by its two named section coordinates.  This turns the ideal-sheaf
definition of the chart into the coordinate-ring presentation used by the
regular-sequence fibre calculation. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIsoSpecQuotient
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subscheme ≅
      AlgebraicGeometry.Spec (.of
        (Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤) ⧸
          (Ideal.span
            {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
              f C seed ij).1} ⊔
            Ideal.span
              {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
                f C seed ij).2}))) := by
  let X := (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  let J : Ideal Γ(X, ⊤) :=
    Ideal.span
      {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1} ⊔
      Ideal.span
        {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
          f C seed ij).2}
  let eI := AllCharacteristics.idealSubschemeIsoSpecQuotient I
  have hIJ : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J := by
    change I.ideal ⟨⊤, isAffineOpen_top X⟩ = _
    rw [show I = AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop J by
      exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_eq_coordinates
        f C seed ij]
    simp
  let eJ := Ideal.quotEquivOfEq hIJ
  exact eI ≪≫ AlgebraicGeometry.Scheme.Spec.mapIso eJ.toCommRingCatIso.symm.op

/-- The quotient presentation of a normalized local pencil zero chart is
compatible with its closed immersion into the ambient product chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIsoSpecQuotient_hom_comp
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIsoSpecQuotient
      f C seed ij).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk
          (Ideal.span
            {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
              f C seed ij).1} ⊔
            Ideal.span
              {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
                f C seed ij).2}))) =
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).isoSpec.hom := by
  let X := (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  let J : Ideal Γ(X, ⊤) :=
    Ideal.span
      {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1} ⊔
      Ideal.span
        {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
          f C seed ij).2}
  let eI := AllCharacteristics.idealSubschemeIsoSpecQuotient I
  have hIJ : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J := by
    change I.ideal ⟨⊤, isAffineOpen_top X⟩ = _
    rw [show I = AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop J by
      exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_eq_coordinates
        f C seed ij]
    simp
  let eJ := Ideal.quotEquivOfEq hIJ
  have hmap : CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ eJ.toCommRingCatIso.symm.hom =
      CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩)) := by
    ext x
    change eJ.symm (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩) x
    simpa only [eJ, Ideal.quotEquivOfEq_symm] using
      Ideal.quotEquivOfEq_mk hIJ.symm x
  have hmap_op : eJ.toCommRingCatIso.symm.op.hom ≫
      (CommRingCat.ofHom (Ideal.Quotient.mk J)).op =
      (CommRingCat.ofHom (Ideal.Quotient.mk
        (I.ideal ⟨⊤, isAffineOpen_top X⟩))).op := by
    apply Opposite.unop_injective
    exact hmap
  change (eI ≪≫ AlgebraicGeometry.Scheme.Spec.mapIso eJ.toCommRingCatIso.symm.op).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = _
  dsimp only [Iso.trans_hom]
  rw [Category.assoc, AlgebraicGeometry.Scheme.Spec.mapIso_hom]
  change eI.hom ≫ (AlgebraicGeometry.Scheme.Spec.map eJ.toCommRingCatIso.symm.op.hom ≫
      AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)).op) = _
  rw [← AlgebraicGeometry.Scheme.Spec.map_comp, hmap_op]
  exact AllCharacteristics.idealSubschemeIsoSpecQuotient_hom_comp I

/-- The normalized local zero chart, in its coordinate-quotient presentation,
maps to the affine parameter-line chart by the quotient of the chart map. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIsoSpecQuotient_hom_comp_toLineChart_isoSpec
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIsoSpecQuotient
      f C seed ij).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk
          (Ideal.span
            {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
              f C seed ij).1} ⊔
            Ideal.span
              {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
                f C seed ij).2})).comp
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
            f C ij).appTop.hom)) =
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij ≫
        ((lineProjOpenCover K).X ij.2).isoSpec.hom := by
  let X := (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  let J : Ideal Γ(X, ⊤) :=
    Ideal.span
      {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1} ⊔
      Ideal.span
        {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
          f C seed ij).2}
  let g := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij
  let eI := AllCharacteristics.idealSubschemeIsoSpecQuotient I
  have hIJ : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J := by
    rw [show I = AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop J by
      exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_eq_coordinates
        f C seed ij]
    simp
  let eJ := Ideal.quotEquivOfEq hIJ
  have hmap : CommRingCat.ofHom ((Ideal.Quotient.mk J).comp g.appTop.hom) ≫
      eJ.toCommRingCatIso.symm.hom =
      CommRingCat.ofHom
        ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩)).comp g.appTop.hom) := by
    ext x
    change eJ.symm (Ideal.Quotient.mk J (g.appTop.hom x)) =
      Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩) (g.appTop.hom x)
    simpa only [eJ, Ideal.quotEquivOfEq_symm] using
      Ideal.quotEquivOfEq_mk hIJ.symm (g.appTop.hom x)
  have hmap_op : eJ.toCommRingCatIso.symm.op.hom ≫
      (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp g.appTop.hom)).op =
      (CommRingCat.ofHom
        ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩)).comp g.appTop.hom)).op := by
    apply Opposite.unop_injective
    exact hmap
  change (eI ≪≫ AlgebraicGeometry.Scheme.Spec.mapIso eJ.toCommRingCatIso.symm.op).hom ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp g.appTop.hom)) = _
  dsimp only [Iso.trans_hom]
  rw [Category.assoc, AlgebraicGeometry.Scheme.Spec.mapIso_hom]
  change eI.hom ≫ (AlgebraicGeometry.Scheme.Spec.map eJ.toCommRingCatIso.symm.op.hom ≫
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp g.appTop.hom)).op) = _
  rw [← AlgebraicGeometry.Scheme.Spec.map_comp, hmap_op]
  exact AllCharacteristics.idealSubschemeIsoSpecQuotient_hom_comp_to_isoSpec g I

/-- Local quasi-finiteness of the coordinate quotient over the affine
parameter chart transfers to the actual normalized local pencil zero scheme. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZero_toLineChart_of_quotient
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    [LocallyQuasiFinite (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk
        (Ideal.span
          {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
            f C seed ij).1} ⊔
          Ideal.span
            {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
              f C seed ij).2})).comp
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
          f C ij).appTop.hom)))] :
    LocallyQuasiFinite
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
  apply AllCharacteristics.locallyQuasiFinite_of_iso_square
    ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subschemeι ≫
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij)
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk
        (Ideal.span
          {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
            f C seed ij).1} ⊔
          Ideal.span
            {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
              f C seed ij).2})).comp
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
          f C ij).appTop.hom)))
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIsoSpecQuotient
      f C seed ij)
    ((lineProjOpenCover K).X ij.2).isoSpec
  exact
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIsoSpecQuotient_hom_comp_toLineChart_isoSpec
      f C seed ij

/-- If the original surface family is locally of finite type, the normalized
zero scheme on every product chart is locally of finite type over its affine
parameter-line chart. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyOfFiniteType_projectiveLineNormalizedLocalPencilZero_toLineChart
    [IsSeparated f] [LocallyOfFiniteType f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    LocallyOfFiniteType
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
  let g := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij
  letI : LocallyOfFiniteType g := by
    change LocallyOfFiniteType (pullback.snd ((C.U ij.1).ι ≫ f)
      ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K))
    infer_instance
  change LocallyOfFiniteType
    ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subschemeι ≫ g)
  infer_instance

/-- The quotient presentation of a normalized local zero scheme is locally
of finite type over the parameter chart whenever the original surface family
is.  This transports finite type across the affine source and target
isomorphisms of the quotient presentation. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyOfFiniteType_projectiveLineNormalizedLocalPencilZero_quotient_toLineChart
    [IsSeparated f] [LocallyOfFiniteType f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    LocallyOfFiniteType (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk
        (Ideal.span
          {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
            f C seed ij).1} ⊔
          Ideal.span
            {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
              f C seed ij).2})).comp
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
          f C ij).appTop.hom))) := by
  let g := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij
  let z := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij).subschemeι ≫ g
  let q := AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk
      (Ideal.span
        {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
          f C seed ij).1} ⊔
        Ideal.span
          {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
            f C seed ij).2})).comp g.appTop.hom))
  letI : LocallyOfFiniteType z :=
    SerreExtensionRankTwoAffineCover.locallyOfFiniteType_projectiveLineNormalizedLocalPencilZero_toLineChart
      f C seed ij
  let eX := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIsoSpecQuotient
    f C seed ij
  let eY := ((lineProjOpenCover K).X ij.2).isoSpec
  have hcomp : eX.hom ≫ q = z ≫ eY.hom := by
    change (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIsoSpecQuotient
      f C seed ij).hom ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk
            (Ideal.span
              {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
                f C seed ij).1} ⊔
              Ideal.span
                {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
                  f C seed ij).2})).comp
            (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
              f C ij).appTop.hom)) =
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed ij).subschemeι ≫
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) ≫
          ((lineProjOpenCover K).X ij.2).isoSpec.hom
    exact
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIsoSpecQuotient_hom_comp_toLineChart_isoSpec
        f C seed ij
  have hq : q = eX.inv ≫ z ≫ eY.hom := by
    calc
      q = 𝟙 _ ≫ q := (Category.id_comp _).symm
      _ = (eX.inv ≫ eX.hom) ≫ q := by rw [eX.inv_hom_id]
      _ = eX.inv ≫ (eX.hom ≫ q) := by simp only [Category.assoc]
      _ = eX.inv ≫ (z ≫ eY.hom) := by rw [hcomp]
      _ = eX.inv ≫ z ≫ eY.hom := Category.assoc _ _ _
  change LocallyOfFiniteType q
  rw [hq]
  infer_instance

/-- Artinianness of the two-coordinate quotients on every residue-field
fiber of an affine product chart proves local quasi-finiteness of the actual
normalized pencil zero scheme.  The quotient presentation transports the
coordinate-ring calculation to the scheme-theoretic zero locus. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZero_toLineChart_of_artinian_coordinate_quotients
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    [LocallyOfFiniteType (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk
        (Ideal.span
          {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
            f C seed ij).1} ⊔
          Ideal.span
            {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
              f C seed ij).2})).comp
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
          f C ij).appTop.hom)))]
    (hartinian :
      let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
      let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
      let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2
      letI : Algebra R S :=
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
      ∀ p : PrimeSpectrum R,
        IsArtinianRing
          ((p.asIdeal.Fiber S) ⧸
            (Ideal.span ({(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) ⊔
              Ideal.span ({(1 ⊗ₜ[R] b : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S))))) :
    LocallyQuasiFinite
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
  let g := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij
  letI : Algebra Γ((lineProjOpenCover K).X ij.2, ⊤)
      Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤) :=
    g.appTop.hom.toAlgebra
  letI : LocallyOfFiniteType (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (algebraMap Γ((lineProjOpenCover K).X ij.2, ⊤)
        (Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤) ⧸
          (Ideal.span
            {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
              f C seed ij).1} ⊔
            Ideal.span
              {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
                f C seed ij).2}))))) := by
    change LocallyOfFiniteType (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk
        (Ideal.span
          {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
            f C seed ij).1} ⊔
          Ideal.span
            {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
              f C seed ij).2})).comp g.appTop.hom)))
    infer_instance
  letI : LocallyQuasiFinite (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (algebraMap Γ((lineProjOpenCover K).X ij.2, ⊤)
        (Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤) ⧸
          (Ideal.span
            {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
              f C seed ij).1} ⊔
            Ideal.span
              {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
                f C seed ij).2}))))) :=
    AllCharacteristics.locallyQuasiFinite_spec_quotient_pair_of_isArtinianRing
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2 hartinian
  change LocallyQuasiFinite
    ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subschemeι ≫ g)
  apply SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZero_toLineChart_of_quotient
    f C seed ij

/-- The affine coordinate-ring data needed to prove quasi-finiteness on one
product chart.  It records the locally finite-type quotient presentation and
the Artinian residue-field coordinate quotients supplied by the regular-pair
calculation. -/
structure SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateQuotientArtinianFibers
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) : Prop where
  locallyOfFiniteType : LocallyOfFiniteType (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk
      (Ideal.span
        {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
          f C seed ij).1} ⊔
        Ideal.span
          {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
            f C seed ij).2})).comp
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
        f C ij).appTop.hom)))
  fiber_artinian :
    let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
    let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
    let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
      f C seed ij).1
    let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
      f C seed ij).2
    letI : Algebra R S :=
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
    ∀ p : PrimeSpectrum R,
      IsArtinianRing
        ((p.asIdeal.Fiber S) ⧸
          (Ideal.span ({(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) ⊔
            Ideal.span ({(1 ⊗ₜ[R] b : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S))))

/-- The residue-field coordinate quotient calculation on one product chart.
When the original surface family is locally of finite type, this is the only
local input still needed for quasi-finiteness: finite type of the quotient
presentation follows formally from the family. -/
structure SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) : Prop where
  fiber_artinian :
    let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
    let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
    let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
      f C seed ij).1
    let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
      f C seed ij).2
    letI : Algebra R S :=
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
    ∀ p : PrimeSpectrum R,
      IsArtinianRing
        ((p.asIdeal.Fiber S) ⧸
          (Ideal.span ({(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) ⊔
            Ideal.span ({(1 ⊗ₜ[R] b : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S))))

/-- On one actual product chart, fibrewise regularity and the dimension-two
localizations of each residue-field surface fibre give the Artinian quotient
calculation required for the normalized pencil.  This is the point where the
smooth-cubic local-dimension theorem feeds into the scheme-level pencil. -/
theorem
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_fibrewiseRegularCoordinates_of_all_maximal_localizations_dim_two
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hnoetherian :
      let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
      let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
      letI : Algebra R S :=
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
      ∀ p : PrimeSpectrum R, IsNoetherianRing (p.asIdeal.Fiber S))
    (hregular :
      let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
      let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
      let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2
      letI : Algebra R S :=
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
      ∀ p : PrimeSpectrum R, AllCharacteristics.IsFibrewiseRegularPair
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))
        (1 ⊗ₜ[R] a : p.asIdeal.Fiber S) (1 ⊗ₜ[R] b))
    (hdim :
      let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
      let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
      letI : Algebra R S :=
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
      ∀ (p : PrimeSpectrum R) (Q : Ideal (p.asIdeal.Fiber S)) [Q.IsMaximal],
        ringKrullDim (Localization.AtPrime Q) = 2) :
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers
      f C seed ij := by
  let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
  let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
  let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).1
  let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).2
  letI : Algebra R S :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
  refine ⟨?_⟩
  change ∀ p : PrimeSpectrum R,
    IsArtinianRing
      ((p.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S))))
  intro p
  letI : IsNoetherianRing (p.asIdeal.Fiber S) := hnoetherian p
  exact AllCharacteristics.isArtinianRing_quotient_pair_fiber_of_fibrewiseRegularPair_of_all_maximal_localizations_dim_two
    p a b (hregular p) (hdim p)

/-- For a locally finite-type surface family, noetherianity of the residue
fibres in the chartwise Artinian calculation is automatic. -/
theorem
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_fibrewiseRegularCoordinates_of_all_maximal_localizations_dim_two_ofLocallyOfFiniteType
    [IsSeparated f] [LocallyOfFiniteType f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hregular :
      let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
      let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
      let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2
      letI : Algebra R S :=
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
      ∀ p : PrimeSpectrum R, AllCharacteristics.IsFibrewiseRegularPair
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))
        (1 ⊗ₜ[R] a : p.asIdeal.Fiber S) (1 ⊗ₜ[R] b))
    (hdim :
      let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
      let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
      letI : Algebra R S :=
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
      ∀ (p : PrimeSpectrum R) (Q : Ideal (p.asIdeal.Fiber S)) [Q.IsMaximal],
        ringKrullDim (Localization.AtPrime Q) = 2) :
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers
      f C seed ij := by
  let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
  let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
  let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).1
  let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).2
  letI : Algebra R S :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
  refine ⟨?_⟩
  change ∀ p : PrimeSpectrum R,
    IsArtinianRing
      ((p.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S))))
  intro p
  letI : LocallyOfFiniteType ((C.U ij.1).ι ≫ f) := inferInstance
  letI : LocallyOfFiniteType
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
    change LocallyOfFiniteType (pullback.snd ((C.U ij.1).ι ≫ f)
      ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K))
    infer_instance
  letI : Algebra.FiniteType R S :=
    HasRingHomProperty.appTop _ _
      (inferInstance : LocallyOfFiniteType
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij))
  exact
    AllCharacteristics.isArtinianRing_quotient_pair_fiber_of_fibrewiseRegularPair_of_finiteType_of_all_maximal_localizations_dim_two
      p a b (hregular p) (hdim p)

/-- Fibrewise regularity on the actual product chart automatically transports
to every residue-field fibre.  Thus a locally finite-type surface chart needs
only one regularity datum, together with the local dimension-two conclusion. -/
theorem
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_base_fibrewiseRegularCoordinates_of_all_maximal_localizations_dim_two_ofLocallyOfFiniteType
    [IsSeparated f] [LocallyOfFiniteType f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hregular :
      let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
      let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
      let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2
      letI : Algebra R S :=
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
      AllCharacteristics.IsFibrewiseRegularPair (algebraMap R S) a b)
    (hdim :
      let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
      let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
      letI : Algebra R S :=
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
      ∀ (p : PrimeSpectrum R) (Q : Ideal (p.asIdeal.Fiber S)) [Q.IsMaximal],
        ringKrullDim (Localization.AtPrime Q) = 2) :
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers
      f C seed ij := by
  let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
  let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
  let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).1
  let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).2
  letI : Algebra R S :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
  exact
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_fibrewiseRegularCoordinates_of_all_maximal_localizations_dim_two_ofLocallyOfFiniteType
      f C seed ij (fun p => hregular.fiber p a b) hdim

/-- The Artinian pencil-fibre calculation only needs the actual residue-field
surface localizations to have Krull dimension at most two. -/
theorem
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_base_fibrewiseRegularCoordinates_of_all_maximal_localizations_dim_le_two_ofLocallyOfFiniteType
    [IsSeparated f] [LocallyOfFiniteType f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hregular :
      let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
      let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
      let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2
      letI : Algebra R S :=
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
      AllCharacteristics.IsFibrewiseRegularPair (algebraMap R S) a b)
    (hdim :
      let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
      let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
      letI : Algebra R S :=
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
      ∀ (p : PrimeSpectrum R) (Q : Ideal (p.asIdeal.Fiber S)) [Q.IsMaximal],
        ringKrullDim (Localization.AtPrime Q) ≤ 2) :
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers
      f C seed ij := by
  let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
  let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
  let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).1
  let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).2
  letI : Algebra R S :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
  refine ⟨?_⟩
  change ∀ p : PrimeSpectrum R,
    IsArtinianRing
      ((p.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S))))
  intro p
  letI : LocallyOfFiniteType ((C.U ij.1).ι ≫ f) := inferInstance
  letI : LocallyOfFiniteType
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
    change LocallyOfFiniteType (pullback.snd ((C.U ij.1).ι ≫ f)
      ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K))
    infer_instance
  letI : Algebra.FiniteType R S :=
    HasRingHomProperty.appTop _ _
      (inferInstance : LocallyOfFiniteType
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij))
  exact
    AllCharacteristics.isArtinianRing_quotient_pair_fiber_of_base_fibrewiseRegularPair_of_finiteType_of_all_maximal_localizations_dim_le_two
      p a b hregular (hdim p)

/-- For a smooth relative surface, the residue-fibre local-dimension input
to the normalized Serre-pencil calculation is automatic. -/
theorem
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_base_fibrewiseRegularCoordinates_of_smoothOfRelativeDimension_two_ofLocallyOfFiniteType
    [IsSeparated f] [LocallyOfFiniteType f] [SmoothOfRelativeDimension 2 f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hregular :
      let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
      let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
      let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2
      letI : Algebra R S :=
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
      AllCharacteristics.IsFibrewiseRegularPair (algebraMap R S) a b) :
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers
      f C seed ij := by
  let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
  let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
  letI : Algebra R S :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
  apply SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_base_fibrewiseRegularCoordinates_of_all_maximal_localizations_dim_le_two_ofLocallyOfFiniteType
    f C seed ij hregular
  change ∀ (p : PrimeSpectrum R) (Q : Ideal (p.asIdeal.Fiber S)) [Q.IsMaximal],
    ringKrullDim (Localization.AtPrime Q) ≤ 2
  intro p Q _
  letI : SmoothOfRelativeDimension 2
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) :=
    SerreExtensionRankTwoAffineCover.smoothOfRelativeDimension_two_projectiveLineOpenCover_toLineChart
      f C ij
  have hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 2)
      (algebraMap R S) := by
    change RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 2)
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom
    exact HasRingHomProperty.appTop _ _
      (inferInstance : SmoothOfRelativeDimension 2
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij))
  exact AllCharacteristics.ringKrullDim_localizationAtPrime_fiber_le_of_locally_standardSmoothOfRelativeDimension
    (R := R) (S := S) 2 hlocal p Q

/-- The local Jacobian/transversality condition for the two normalized
coordinates of one Serre-pencil chart.  The first coordinate is a cotangent
parameter at a common zero and the second remains one after quotienting by
the first. -/
def SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateSuccessiveRegularParameters
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) : Prop :=
  let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
  let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
  let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).1
  let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).2
  letI : Algebra R S :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
  ∀ (p : PrimeSpectrum R) (Q : Ideal (p.asIdeal.Fiber S)) [Q.IsMaximal],
    let T := Localization.AtPrime Q
    let c : T := algebraMap (p.asIdeal.Fiber S) T (1 ⊗ₜ[R] a : p.asIdeal.Fiber S)
    let d : T := algebraMap (p.asIdeal.Fiber S) T (1 ⊗ₜ[R] b)
    let π : T →+* T ⧸ Ideal.span {c} := Ideal.Quotient.mk (Ideal.span {c})
    let m : Ideal T := IsLocalRing.maximalIdeal T
    let M : Ideal (T ⧸ Ideal.span {c}) := m.map π
    (1 ⊗ₜ[R] a : p.asIdeal.Fiber S) ∈ Q → (1 ⊗ₜ[R] b) ∈ Q →
    c ∉ m ^ 2 ∧ π d ∉ M ^ 2

/-- The direct rank-two cotangent condition for the normalized coordinates of
one Serre-pencil chart.  At every common zero their images are independent in
the cotangent space of the residue-field surface. -/
structure SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateCotangentIndependentParameters
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) : Prop where
  parameters :
    let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
    let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
    let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
      f C seed ij).1
    let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
      f C seed ij).2
    letI : Algebra R S :=
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
    ∀ (p : PrimeSpectrum R) (Q : Ideal (p.asIdeal.Fiber S)) [Q.IsMaximal],
      let T := Localization.AtPrime Q
      let c : T := algebraMap (p.asIdeal.Fiber S) T (1 ⊗ₜ[R] a : p.asIdeal.Fiber S)
      let d : T := algebraMap (p.asIdeal.Fiber S) T (1 ⊗ₜ[R] b)
      let m : Ideal T := IsLocalRing.maximalIdeal T
      (1 ⊗ₜ[R] a : p.asIdeal.Fiber S) ∈ Q → (1 ⊗ₜ[R] b : p.asIdeal.Fiber S) ∈ Q →
      c ∉ m ^ 2 ∧ d ∉ Ideal.span {c} ⊔ m ^ 2

/- A unit certificate for the first actual normalized coordinate is already
   enough for the two local outputs used by the projective-line construction.
   The first regularity condition is automatic in the zero quotient, and the
   cotangent condition is vacuous because a unit cannot lie in a proper local
   ideal.  Keeping this at the named-coordinate level lets a later geometric
   argument provide a unit certificate without reopening the sheaf
   trivialization. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates_fibrewiseRegular_of_first_isUnit
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hunit : IsUnit
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1) :
    AllCharacteristics.IsFibrewiseRegularPair
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2 := by
  exact AllCharacteristics.isFibrewiseRegularPair_of_first_isUnit _ _ _ hunit

theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates_cotangentIndependentParameters_of_first_isUnit
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hunit : IsUnit
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1) :
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateCotangentIndependentParameters
      f C seed ij := by
  constructor
  dsimp only
  intro p Q _ hQa hQb
  let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
  let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
  let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).1
  letI : Algebra R S :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
  have hfa' : IsUnit
      ((Algebra.TensorProduct.includeRight (R := R) (A := p.asIdeal.ResidueField)
        (B := S)).toRingHom a) :=
    hunit.map (Algebra.TensorProduct.includeRight (R := R)
      (A := p.asIdeal.ResidueField) (B := S)).toRingHom
  have hfa : IsUnit (1 ⊗ₜ[R] a : p.asIdeal.Fiber S) := by
    change IsUnit ((Algebra.TensorProduct.includeRight (R := R)
      (A := p.asIdeal.ResidueField) (B := S)).toRingHom a)
    exact hfa'
  exact False.elim ((Ideal.notMem_of_isUnit Q hfa) hQa)

/-- Cotangent-space independence implies the successive-parameter condition.
The only algebraic step is that an element outside the span of the first
parameter and the square of the maximal ideal remains outside the square of
the maximal ideal after quotienting by the first parameter. -/
theorem
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateCotangentIndependentParameters.toSuccessiveRegularParameters
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hparameters :
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateCotangentIndependentParameters
        f C seed ij) :
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateSuccessiveRegularParameters
      f C seed ij := by
  let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
  let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
  let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).1
  let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).2
  letI : Algebra R S :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
  change ∀ (p : PrimeSpectrum R) (Q : Ideal (p.asIdeal.Fiber S)) [Q.IsMaximal],
    let T := Localization.AtPrime Q
    let c : T := algebraMap (p.asIdeal.Fiber S) T (1 ⊗ₜ[R] a : p.asIdeal.Fiber S)
    let d : T := algebraMap (p.asIdeal.Fiber S) T (1 ⊗ₜ[R] b)
    let π : T →+* T ⧸ Ideal.span {c} := Ideal.Quotient.mk (Ideal.span {c})
    let m : Ideal T := IsLocalRing.maximalIdeal T
    let M : Ideal (T ⧸ Ideal.span {c}) := m.map π
    (1 ⊗ₜ[R] a : p.asIdeal.Fiber S) ∈ Q → (1 ⊗ₜ[R] b) ∈ Q →
    c ∉ m ^ 2 ∧ π d ∉ M ^ 2
  refine fun p Q _ hpa hpb => ?_
  have hparams := hparameters.parameters
  dsimp only at hparams
  obtain ⟨hc, hd⟩ := hparams p Q hpa hpb
  refine ⟨hc, ?_⟩
  let T := Localization.AtPrime Q
  let c : T := algebraMap (p.asIdeal.Fiber S) T (1 ⊗ₜ[R] a : p.asIdeal.Fiber S)
  let d : T := algebraMap (p.asIdeal.Fiber S) T (1 ⊗ₜ[R] b)
  let m : Ideal T := IsLocalRing.maximalIdeal T
  have hd' : d ∉ Ideal.span {c} ⊔ m ^ 2 := by
    exact hd
  simpa only [T, c, d, m] using
    (AllCharacteristics.quotient_not_mem_mapped_square_of_not_mem_span_sup_square_let m c d hd')

/-- On a smooth relative surface chart, the normalized pencil quotient has
Artinian residue fibres as soon as its two coordinate functions are
successive cotangent-space parameters at every common zero.  Smoothness
supplies both regular local ambient rings and the dimension-two bound, so the
remaining input is exactly the Jacobian/transversality calculation for the
chosen section. -/
theorem
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_local_successiveRegularParameters_of_smoothOfRelativeDimension_two_ofLocallyOfFiniteType
    [IsSeparated f] [LocallyOfFiniteType f] [SmoothOfRelativeDimension 2 f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hparameters :
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateSuccessiveRegularParameters
        f C seed ij) :
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers
      f C seed ij := by
  let R := Γ((lineProjOpenCover K).X ij.2, ⊤)
  let S := Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤)
  let a := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).1
  let b := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
    f C seed ij).2
  letI : Algebra R S :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.toAlgebra
  letI : SmoothOfRelativeDimension 2
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) :=
    SerreExtensionRankTwoAffineCover.smoothOfRelativeDimension_two_projectiveLineOpenCover_toLineChart
      f C ij
  have hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 2)
      (algebraMap R S) := by
    change RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 2)
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom
    exact HasRingHomProperty.appTop _ _
      (inferInstance : SmoothOfRelativeDimension 2
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij))
  refine ⟨?_⟩
  change ∀ p : PrimeSpectrum R,
    IsArtinianRing
      ((p.asIdeal.Fiber S) ⧸
        (Ideal.span ({(1 ⊗ₜ[R] a : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S)) ⊔
          Ideal.span ({(1 ⊗ₜ[R] b : p.asIdeal.Fiber S)} : Set (p.asIdeal.Fiber S))))
  intro p
  letI : LocallyOfFiniteType ((C.U ij.1).ι ≫ f) := inferInstance
  letI : LocallyOfFiniteType
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
    change LocallyOfFiniteType (pullback.snd ((C.U ij.1).ι ≫ f)
      ((lineProjOpenCover K).f ij.2 ≫ projectiveLineProjToBase K))
    infer_instance
  letI : Algebra.FiniteType R S :=
    HasRingHomProperty.appTop _ _
      (inferInstance : LocallyOfFiniteType
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij))
  letI : IsNoetherianRing (p.asIdeal.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField (p.asIdeal.Fiber S)
  apply
    AllCharacteristics.isArtinianRing_quotient_pair_of_successive_regularParameters_at_all_common_maximal_localizations_dim_le_two
      (1 ⊗ₜ[R] a : p.asIdeal.Fiber S) (1 ⊗ₜ[R] b)
  · intro Q _ hp hq
    obtain ⟨hpsquare, hqsquare⟩ := hparameters p Q hp hq
    refine ⟨?_, hpsquare, hqsquare⟩
    exact AllCharacteristics.isRegularLocalRing_localizationAtPrime_fiber_of_locally_standardSmoothOfRelativeDimension
      (R := R) (S := S) 2 hlocal p Q
  · intro Q _
    exact
      AllCharacteristics.ringKrullDim_localizationAtPrime_fiber_le_of_locally_standardSmoothOfRelativeDimension
        (R := R) (S := S) 2 hlocal p Q

/-- On a smooth relative surface chart, the direct rank-two cotangent
condition for the normalized pencil coordinates makes every residue-field
zero-fibre Artinian.  This is the form supplied by a Jacobian rank
calculation, without choosing successive quotient parameters. -/
theorem
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_local_cotangentIndependentParameters_of_smoothOfRelativeDimension_two_ofLocallyOfFiniteType
    [IsSeparated f] [LocallyOfFiniteType f] [SmoothOfRelativeDimension 2 f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hparameters :
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateCotangentIndependentParameters
        f C seed ij) :
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers
      f C seed ij := by
  exact
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_local_successiveRegularParameters_of_smoothOfRelativeDimension_two_ofLocallyOfFiniteType
      f C seed ij
      (SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateCotangentIndependentParameters.toSuccessiveRegularParameters
        f C seed ij hparameters)

/-- A locally finite-type surface family supplies the finite-type field of
the older quotient package automatically. -/
theorem
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateQuotientArtinianFibers.ofLocallyOfFiniteType
    [IsSeparated f] [LocallyOfFiniteType f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hartinian :
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers
        f C seed ij) :
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateQuotientArtinianFibers
      f C seed ij := by
  refine ⟨?_, hartinian.fiber_artinian⟩
  exact
    SerreExtensionRankTwoAffineCover.locallyOfFiniteType_projectiveLineNormalizedLocalPencilZero_quotient_toLineChart
      f C seed ij

/-- Under local finite type of the original surface family, Artinianness of
the two-coordinate residue-field quotients proves local quasi-finiteness of
the actual normalized zero scheme without a separate finite-type premise. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZero_toLineChart_of_artinian_coordinate_fibers
    [IsSeparated f] [LocallyOfFiniteType f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hartinian :
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers
        f C seed ij) :
    LocallyQuasiFinite
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
  let h :=
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateQuotientArtinianFibers.ofLocallyOfFiniteType
      f C seed ij hartinian
  letI : LocallyOfFiniteType _ := h.locallyOfFiniteType
  exact
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZero_toLineChart_of_artinian_coordinate_quotients
      f C seed ij h.fiber_artinian

/-- Pulling a nonconstant coordinate from the left product chart to an
arbitrary product-chart overlap gives the corresponding general-overlap
coordinate. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_pullback_leftCoordinateCoefficient
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    BundleSectionZeroLocus.pullbackUnitEndomorphism
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_pullbackUnitComparison_isIso
        f C ij kl)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij) =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
      f C ij kl (!ij.2) := by
  let p := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  letI : IsOpenImmersion p :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_isOpenImmersion
      f C ij kl
  unfold SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
  rw [BundleSectionZeroLocus.pullbackUnitEndomorphismOfRegularFunction_eq_appTop]
  congr 1

/-- Pulling a nonconstant coordinate from the right product chart to an
arbitrary product-chart overlap gives the corresponding general-overlap
coordinate. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_pullback_rightCoordinateCoefficient
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    BundleSectionZeroLocus.pullbackUnitEndomorphism
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_snd_pullbackUnitComparison_isIso
        f C ij kl)
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C kl) =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
      f C ij kl (!kl.2) := by
  let p := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  letI : IsOpenImmersion p :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_snd_isOpenImmersion
      f C ij kl
  unfold SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
  rw [BundleSectionZeroLocus.pullbackUnitEndomorphismOfRegularFunction_eq_appTop]
  congr 1

/-- The normalized homogeneous coefficient pair described directly on the
left side of a general product-chart overlap. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedLeftCoefficients
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
          f C ij kl).ringCatSheaf) ×
    (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
          f C ij kl).ringCatSheaf) :=
  by
    classical
    exact if ij.2 = true then
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
        f C ij kl (!ij.2), 𝟙 _)
    else
      (𝟙 _, SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
        f C ij kl (!ij.2))

/-- The normalized homogeneous coefficient pair described directly on the
right side of a general product-chart overlap. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedRightCoefficients
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
          f C ij kl).ringCatSheaf) ×
    (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
          f C ij kl).ringCatSheaf) :=
  by
    classical
    exact if kl.2 = true then
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
        f C ij kl (!kl.2), 𝟙 _)
    else
      (𝟙 _, SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
        f C ij kl (!kl.2))

/-- The normalized homogeneous coefficients from the left product chart,
restricted to an arbitrary product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedCoefficients
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
          f C ij kl).ringCatSheaf) ×
    (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
          f C ij kl).ringCatSheaf) :=
  (BundleSectionZeroLocus.pullbackUnitEndomorphism
    (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_pullbackUnitComparison_isIso f C ij kl)
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C ij).1,
   BundleSectionZeroLocus.pullbackUnitEndomorphism
    (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_pullbackUnitComparison_isIso f C ij kl)
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C ij).2)

/-- The normalized homogeneous coefficients from the right product chart,
restricted to an arbitrary product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedCoefficients
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
          f C ij kl).ringCatSheaf) ×
    (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
          f C ij kl).ringCatSheaf) :=
  (BundleSectionZeroLocus.pullbackUnitEndomorphism
    (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_snd_pullbackUnitComparison_isIso f C ij kl)
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C kl).1,
   BundleSectionZeroLocus.pullbackUnitEndomorphism
    (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_snd_pullbackUnitComparison_isIso f C ij kl)
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C kl).2)

/-- The coefficient pair pulled from the left product chart agrees with the
direct coordinate description on a general overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_pullback_normalizedLeftCoefficients
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedCoefficients
      f C ij kl =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedLeftCoefficients
      f C ij kl := by
  classical
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedCoefficients
  cases h : ij.2
  · rw [SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients_of_eq_false
      f C ij h]
    unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedLeftCoefficients
    rw [if_neg (by simp [h])]
    change (_, _) = (_, _)
    rw [BundleSectionZeroLocus.pullbackUnitEndomorphism_id,
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_pullback_leftCoordinateCoefficient]
  · rw [SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients_of_eq_true
      f C ij h]
    unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedLeftCoefficients
    rw [if_pos h]
    change (_, _) = (_, _)
    rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_pullback_leftCoordinateCoefficient,
      BundleSectionZeroLocus.pullbackUnitEndomorphism_id]

/-- The coefficient pair pulled from the right product chart agrees with the
direct coordinate description on a general overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_pullback_normalizedRightCoefficients
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedCoefficients
      f C ij kl =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedRightCoefficients
      f C ij kl := by
  classical
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedCoefficients
  cases h : kl.2
  · rw [SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients_of_eq_false
      f C kl h]
    unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedRightCoefficients
    rw [if_neg (by simp [h])]
    change (_, _) = (_, _)
    rw [BundleSectionZeroLocus.pullbackUnitEndomorphism_id,
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_pullback_rightCoordinateCoefficient]
  · rw [SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients_of_eq_true
      f C kl h]
    unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedRightCoefficients
    rw [if_pos h]
    change (_, _) = (_, _)
    rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_pullback_rightCoordinateCoefficient,
      BundleSectionZeroLocus.pullbackUnitEndomorphism_id]

/-- On the nontrivial parameter-chart overlap, the two directly described
normalized coefficient pairs differ by the common invertible projective
transition factor. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_normalizedCoefficients_commonScale
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 ≠ kl.2) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedLeftCoefficients
      f C ij kl =
      (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit f C ij kl) ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedRightCoefficients
          f C ij kl).1,
       BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit f C ij kl) ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedRightCoefficients
      f C ij kl).2) := by
  classical
  unfold
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedLeftCoefficients
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedRightCoefficients
  rcases ij with ⟨i, b⟩
  rcases kl with ⟨j, c⟩
  cases b <;> cases c
  · exact False.elim (hij rfl)
  · rw [if_neg (by
      change false ≠ true
      decide), if_pos (by
      change true = true
      rfl)]
    change
      (𝟙 _,
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
          f C (i, false) (j, true) true) =
      (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
            f C (i, false) (j, true)) ≫
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
            f C (i, false) (j, true) false,
       BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
            f C (i, false) (j, true)) ≫ 𝟙 _)
    apply Prod.ext
    · exact
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_leftCoordinateCoefficient_self
          f C (i, false) (j, true)).symm.trans
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_coordinateCoefficient_relation
            f C (i, false) (j, true) false)
    · calc
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
            f C (i, false) (j, true) true =
          BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, false) (j, true)) ≫
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
              f C (i, false) (j, true) true :=
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_coordinateCoefficient_relation
            f C (i, false) (j, true) true
        _ = BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, false) (j, true)) ≫ 𝟙 _ := by
          exact congrArg (fun t =>
            BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, false) (j, true)) ≫ t)
            (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_rightCoordinateCoefficient_self
              f C (i, false) (j, true))
  · rw [if_pos (by
      change true = true
      rfl), if_neg (by
      change false ≠ true
      decide)]
    change
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
          f C (i, true) (j, false) false, 𝟙 _) =
      (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
            f C (i, true) (j, false)) ≫ 𝟙 _,
       BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
            f C (i, true) (j, false)) ≫
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
            f C (i, true) (j, false) true)
    apply Prod.ext
    · calc
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
            f C (i, true) (j, false) false =
          BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, true) (j, false)) ≫
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
              f C (i, true) (j, false) false :=
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_coordinateCoefficient_relation
            f C (i, true) (j, false) false
        _ = BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, true) (j, false)) ≫ 𝟙 _ := by
          exact congrArg (fun t =>
            BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, true) (j, false)) ≫ t)
            (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_rightCoordinateCoefficient_self
              f C (i, true) (j, false))
    · exact
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_leftCoordinateCoefficient_self
          f C (i, true) (j, false)).symm.trans
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_coordinateCoefficient_relation
            f C (i, true) (j, false) true)
  · exact False.elim (hij rfl)

/-- The left normalized pencil equation on an arbitrary product-chart
intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilSection
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalModule
      f C ij kl).sections :=
  BundleSectionZeroLocus.addSections
    (BundleSectionZeroLocus.scaleSection
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedCoefficients f C ij kl).1
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalCanonicalSection f C ij kl))
    (BundleSectionZeroLocus.scaleSection
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedCoefficients f C ij kl).2
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalLiftSection f C seed ij kl))

/-- The right normalized pencil equation on an arbitrary product-chart
intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilSection
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalModule
      f C ij kl).sections :=
  BundleSectionZeroLocus.addSections
    (BundleSectionZeroLocus.scaleSection
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedCoefficients f C ij kl).1
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalCanonicalSection f C ij kl))
    (BundleSectionZeroLocus.scaleSection
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedCoefficients f C ij kl).2
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalLiftSection f C seed ij kl))

/-- A normalized Serre-pencil equation on a general product-chart overlap,
expressed in the common restricted module. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonPencilSectionOfCoefficients
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (a : (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl).ringCatSheaf) ×
      (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl).ringCatSheaf)) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLocalModule
      f C ij kl).sections :=
  BundleSectionZeroLocus.addSections
    (BundleSectionZeroLocus.scaleSection a.1
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection
        f C e.canonicalSection ij kl))
    (BundleSectionZeroLocus.scaleSection a.2
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection
        f C seed.lift ij kl))

/-- The left normalized equation, expressed in the common restricted
module on a general product-chart overlap. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLeftNormalizedPencilSection
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLocalModule
      f C ij kl).sections :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonPencilSectionOfCoefficients
    f C seed ij kl
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedCoefficients
      f C ij kl)

/-- The right normalized equation, expressed in the common restricted
module on a general product-chart overlap. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonRightNormalizedPencilSection
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLocalModule
      f C ij kl).sections :=
  SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonPencilSectionOfCoefficients
    f C seed ij kl
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedCoefficients
      f C ij kl)

/-- Transporting the common left normalized equation gives precisely the
left local normalized equation. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLeftNormalizedPencilSection_toLeftLocal
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.sectionsMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToLeftLocalModuleIso
        f C ij kl).hom
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLeftNormalizedPencilSection
        f C seed ij kl) =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilSection
      f C seed ij kl := by
  unfold
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLeftNormalizedPencilSection
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonPencilSectionOfCoefficients
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilSection
  rw [BundleSectionZeroLocus.sectionsMap_addSections,
    BundleSectionZeroLocus.sectionsMap_scaleSection,
    BundleSectionZeroLocus.sectionsMap_scaleSection,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection_toLeftLocal,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection_toLeftLocal]
  rfl

/-- Transporting the common right normalized equation gives precisely the
right local normalized equation. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonRightNormalizedPencilSection_toRightLocal
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SheafOfModules.sectionsMap
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToRightLocalModuleIso
        f C ij kl).hom
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonRightNormalizedPencilSection
        f C seed ij kl) =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilSection
      f C seed ij kl := by
  unfold
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonRightNormalizedPencilSection
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonPencilSectionOfCoefficients
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilSection
  rw [BundleSectionZeroLocus.sectionsMap_addSections,
    BundleSectionZeroLocus.sectionsMap_scaleSection,
    BundleSectionZeroLocus.sectionsMap_scaleSection,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection_toRightLocal,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonSection_toRightLocal]
  rfl

/-- Common rescaling of a pair of homogeneous coefficients rescales the
corresponding common-overlap pencil equation. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonPencilSectionOfCoefficients_commonScale
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (u : SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl).ringCatSheaf)
    (a : (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl).ringCatSheaf) ×
      (SheafOfModules.unit
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl).ringCatSheaf ⟶
      SheafOfModules.unit
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl).ringCatSheaf)) :
    BundleSectionZeroLocus.scaleSection u
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonPencilSectionOfCoefficients
        f C seed ij kl a) =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonPencilSectionOfCoefficients
      f C seed ij kl (u ≫ a.1, u ≫ a.2) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonPencilSectionOfCoefficients
  rw [BundleSectionZeroLocus.scaleSection_addSections,
    BundleSectionZeroLocus.scaleSection_scaleSection,
    BundleSectionZeroLocus.scaleSection_scaleSection]

/-- On the nontrivial projective-line overlap, the two common normalized
equations differ by the invertible projective transition scalar. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommon_normalizedPencilSection_commonScale
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 ≠ kl.2) :
    BundleSectionZeroLocus.scaleSection
      (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit f C ij kl))
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonRightNormalizedPencilSection
        f C seed ij kl) =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLeftNormalizedPencilSection
      f C seed ij kl := by
  unfold
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLeftNormalizedPencilSection
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonRightNormalizedPencilSection
  rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_pullback_normalizedLeftCoefficients,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_pullback_normalizedRightCoefficients,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_normalizedCoefficients_commonScale
      f C ij kl hij]
  exact
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonPencilSectionOfCoefficients_commonScale
      f C seed ij kl _ _

/-- If two product charts use the same projective-line chart, their direct
normalized coefficient pairs agree exactly. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_normalizedCoefficients_eq_of_eq
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 = kl.2) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedLeftCoefficients
      f C ij kl =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedRightCoefficients
      f C ij kl := by
  rcases ij with ⟨i, b⟩
  rcases kl with ⟨j, c⟩
  cases b <;> cases c
  · unfold
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedLeftCoefficients
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedRightCoefficients
    rw [if_neg (by simp), if_neg (by simp)]
    apply Prod.ext
    · rfl
    · have hu : (𝟙 _) = BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
            f C (i, false) (j, false)) := by
        calc
          𝟙 _ = SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
              f C (i, false) (j, false) false :=
            (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_leftCoordinateCoefficient_self
              f C (i, false) (j, false)).symm
          _ = BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, false) (j, false)) ≫
              SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
                f C (i, false) (j, false) false :=
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_coordinateCoefficient_relation
              f C (i, false) (j, false) false
          _ = BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, false) (j, false)) ≫ 𝟙 _ := by
            exact congrArg (fun q => BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, false) (j, false)) ≫ q)
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_rightCoordinateCoefficient_self
                f C (i, false) (j, false))
          _ = BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, false) (j, false)) := Category.comp_id _
      calc
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
            f C (i, false) (j, false) true =
          BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, false) (j, false)) ≫
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
              f C (i, false) (j, false) true :=
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_coordinateCoefficient_relation
            f C (i, false) (j, false) true
        _ = 𝟙 _ ≫ SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
              f C (i, false) (j, false) true := by
          exact congrArg (fun q => q ≫
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
              f C (i, false) (j, false) true) hu.symm
        _ = SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
              f C (i, false) (j, false) true := Category.id_comp _
  · exact False.elim (by simpa using hij)
  · exact False.elim (by simpa using hij)
  · unfold
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedLeftCoefficients
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapNormalizedRightCoefficients
    rw [if_pos rfl, if_pos rfl]
    apply Prod.ext
    · have hu : (𝟙 _) = BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
            f C (i, true) (j, true)) := by
        calc
          𝟙 _ = SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
              f C (i, true) (j, true) true :=
            (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_leftCoordinateCoefficient_self
              f C (i, true) (j, true)).symm
          _ = BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, true) (j, true)) ≫
              SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
                f C (i, true) (j, true) true :=
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_coordinateCoefficient_relation
              f C (i, true) (j, true) true
          _ = BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, true) (j, true)) ≫ 𝟙 _ := by
            exact congrArg (fun q => BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, true) (j, true)) ≫ q)
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_rightCoordinateCoefficient_self
                f C (i, true) (j, true))
          _ = BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, true) (j, true)) := Category.comp_id _
      calc
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftCoordinateCoefficient
            f C (i, true) (j, true) false =
          BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit
                f C (i, true) (j, true)) ≫
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
              f C (i, true) (j, true) false :=
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_coordinateCoefficient_relation
            f C (i, true) (j, true) false
        _ = 𝟙 _ ≫ SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
              f C (i, true) (j, true) false := by
          exact congrArg (fun q => q ≫
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
              f C (i, true) (j, true) false) hu.symm
        _ = SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightCoordinateCoefficient
              f C (i, true) (j, true) false := Category.id_comp _
    · rfl

/-- If two product charts use the same projective-line chart, their common
normalized pencil sections agree exactly. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommon_normalizedPencilSection_eq_of_eq
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 = kl.2) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLeftNormalizedPencilSection
      f C seed ij kl =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonRightNormalizedPencilSection
      f C seed ij kl := by
  unfold
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLeftNormalizedPencilSection
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonRightNormalizedPencilSection
  rw [SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_pullback_normalizedLeftCoefficients,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_pullback_normalizedRightCoefficients,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_normalizedCoefficients_eq_of_eq
      f C ij kl hij]

/-- The coordinate zero ideal of the left normalized equation on an arbitrary
product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilZeroIdeal
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    AlgebraicGeometry.Scheme.IdealSheafData
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalFreeIso
      f C ij kl)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilSection
      f C seed ij kl)

/-- The coordinate zero ideal of the right normalized equation on an
arbitrary product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilZeroIdeal
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    AlgebraicGeometry.Scheme.IdealSheafData
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
        f C ij kl) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalFreeIso
      f C ij kl)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilSection
      f C seed ij kl)

/-- On a nontrivial projective-line transition, the two normalized coordinate
zero ideals agree on every general product-chart overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_normalizedPencilZeroIdeal_eq
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 ≠ kl.2) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilZeroIdeal
      f C seed ij kl =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilZeroIdeal
      f C seed ij kl := by
  let T := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl
  let cL := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToLeftLocalModuleIso
    f C ij kl
  let cR := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToRightLocalModuleIso
    f C ij kl
  let eL := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalFreeIso
    f C ij kl
  let eR := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalFreeIso
    f C ij kl
  let sL := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilSection
    f C seed ij kl
  let sR := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilSection
    f C seed ij kl
  let tL := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLeftNormalizedPencilSection
    f C seed ij kl
  let tR := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonRightNormalizedPencilSection
    f C seed ij kl
  let u := BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapUnit f C ij kl)
  let eLC := eL ≪≫ cL.symm
  let eRC := eR ≪≫ cR.symm
  haveI : IsAffine T :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_affine f C ij kl
  haveI : IsIso u :=
    SerreExtensionRankTwoAffineCover.isIso_projectiveLineOpenCoverGeneralOverlapUnitCoefficient
      f C ij kl
  have hL : SheafOfModules.sectionsMap cL.inv sL = tL := by
    have hforward : SheafOfModules.sectionsMap cL.hom tL = sL := by
      exact
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLeftNormalizedPencilSection_toLeftLocal
          f C seed ij kl
    calc
      SheafOfModules.sectionsMap cL.inv sL =
          SheafOfModules.sectionsMap cL.inv
            (SheafOfModules.sectionsMap cL.hom tL) := by rw [hforward]
      _ = SheafOfModules.sectionsMap (cL.hom ≫ cL.inv) tL :=
        (SheafOfModules.sectionsMap_comp cL.hom cL.inv tL).symm
      _ = SheafOfModules.sectionsMap (𝟙 _) tL :=
        congrArg (fun q => SheafOfModules.sectionsMap q tL) cL.hom_inv_id
      _ = tL := SheafOfModules.sectionsMap_id tL
  have hR : SheafOfModules.sectionsMap cR.inv sR = tR := by
    have hforward : SheafOfModules.sectionsMap cR.hom tR = sR := by
      exact
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonRightNormalizedPencilSection_toRightLocal
          f C seed ij kl
    calc
      SheafOfModules.sectionsMap cR.inv sR =
          SheafOfModules.sectionsMap cR.inv
            (SheafOfModules.sectionsMap cR.hom tR) := by rw [hforward]
      _ = SheafOfModules.sectionsMap (cR.hom ≫ cR.inv) tR :=
        (SheafOfModules.sectionsMap_comp cR.hom cR.inv tR).symm
      _ = SheafOfModules.sectionsMap (𝟙 _) tR :=
        congrArg (fun q => SheafOfModules.sectionsMap q tR) cR.hom_inv_id
      _ = tR := SheafOfModules.sectionsMap_id tR
  have hscale : BundleSectionZeroLocus.scaleSection u tR = tL := by
    exact
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommon_normalizedPencilSection_commonScale
        f C seed ij kl hij
  change BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eL sL =
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eR sR
  calc
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eL sL =
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eLC
        (SheafOfModules.sectionsMap cL.inv sL) :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq
        (ULift.{u} (Fin 2)) eL cL.symm sL
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eLC tL := by
      rw [hL]
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eLC
        (BundleSectionZeroLocus.scaleSection u tR) := by rw [hscale]
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eLC tR :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso
        (ULift.{u} (Fin 2)) eLC u tR
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eRC tR :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso
        (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) eLC eRC tR
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eRC
        (SheafOfModules.sectionsMap cR.inv sR) := by rw [hR]
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eR sR :=
      (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq
        (ULift.{u} (Fin 2)) eR cR.symm sR).symm

theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_normalizedPencilZeroIdeal_eq_of_eq
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 = kl.2) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilZeroIdeal
      f C seed ij kl =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilZeroIdeal
      f C seed ij kl := by
  let T := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap f C ij kl
  let cL := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToLeftLocalModuleIso
    f C ij kl
  let cR := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonToRightLocalModuleIso
    f C ij kl
  let eL := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalFreeIso
    f C ij kl
  let eR := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalFreeIso
    f C ij kl
  let sL := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilSection
    f C seed ij kl
  let sR := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilSection
    f C seed ij kl
  let tL := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLeftNormalizedPencilSection
    f C seed ij kl
  let tR := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonRightNormalizedPencilSection
    f C seed ij kl
  let eLC := eL ≪≫ cL.symm
  let eRC := eR ≪≫ cR.symm
  haveI : IsAffine T :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_affine f C ij kl
  have hL : SheafOfModules.sectionsMap cL.inv sL = tL := by
    have hforward : SheafOfModules.sectionsMap cL.hom tL = sL := by
      exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonLeftNormalizedPencilSection_toLeftLocal
        f C seed ij kl
    calc
      SheafOfModules.sectionsMap cL.inv sL =
          SheafOfModules.sectionsMap cL.inv
            (SheafOfModules.sectionsMap cL.hom tL) := by rw [hforward]
      _ = SheafOfModules.sectionsMap (cL.hom ≫ cL.inv) tL :=
        (SheafOfModules.sectionsMap_comp cL.hom cL.inv tL).symm
      _ = SheafOfModules.sectionsMap (𝟙 _) tL :=
        congrArg (fun q => SheafOfModules.sectionsMap q tL) cL.hom_inv_id
      _ = tL := SheafOfModules.sectionsMap_id tL
  have hR : SheafOfModules.sectionsMap cR.inv sR = tR := by
    have hforward : SheafOfModules.sectionsMap cR.hom tR = sR := by
      exact SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommonRightNormalizedPencilSection_toRightLocal
        f C seed ij kl
    calc
      SheafOfModules.sectionsMap cR.inv sR =
          SheafOfModules.sectionsMap cR.inv
            (SheafOfModules.sectionsMap cR.hom tR) := by rw [hforward]
      _ = SheafOfModules.sectionsMap (cR.hom ≫ cR.inv) tR :=
        (SheafOfModules.sectionsMap_comp cR.hom cR.inv tR).symm
      _ = SheafOfModules.sectionsMap (𝟙 _) tR :=
        congrArg (fun q => SheafOfModules.sectionsMap q tR) cR.hom_inv_id
      _ = tR := SheafOfModules.sectionsMap_id tR
  have hcommon : tL = tR := by
    exact
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapCommon_normalizedPencilSection_eq_of_eq
        f C seed ij kl hij
  change BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eL sL =
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eR sR
  calc
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eL sL =
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eLC
        (SheafOfModules.sectionsMap cL.inv sL) :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq
        (ULift.{u} (Fin 2)) eL cL.symm sL
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eLC tL := by rw [hL]
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eLC tR := by rw [hcommon]
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eRC tR :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso
        (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) eLC eRC tR
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eRC
        (SheafOfModules.sectionsMap cR.inv sR) := by rw [hR]
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eR sR :=
      (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq
        (ULift.{u} (Fin 2)) eR cR.symm sR).symm


/-- The normalized coordinate zero ideals agree on every intersection of two
affine product charts, whether or not the projective-line charts differ. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_normalizedPencilZeroIdeal_eq_all
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilZeroIdeal
      f C seed ij kl =
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilZeroIdeal
      f C seed ij kl := by
  by_cases hij : ij.2 = kl.2
  · exact
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_normalizedPencilZeroIdeal_eq_of_eq
        f C seed ij kl hij
  · exact
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_normalizedPencilZeroIdeal_eq
        f C seed ij kl hij

/-- Restricting a normalized local pencil zero ideal to an arbitrary product-chart
overlap gives its left local presentation on that overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_comap_fst
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).comap
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilZeroIdeal
        f C seed ij kl := by
  let p := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let q := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C ij
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
    (e.E.over (C.U ij.1))
  let A := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback p).app
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij)
  let B := (AlgebraicGeometry.Scheme.Modules.pullbackComp p q).app E
  let c := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftRestrictionToLocalModuleIso
    f C ij kl
  let eL := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalFreeIso
    f C ij kl
  let sL := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilSection
    f C seed ij kl
  let eLocal := SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij
  let s := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection f C seed ij
  let eC := BundleSectionZeroLocus.restrictionFreeIsoOf p (ULift.{u} (Fin 2)) eLocal
  let sC := BundleSectionZeroLocus.restrictModuleSection p
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) s
  haveI : IsAffine (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
      f C ij kl) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_affine f C ij kl
  haveI : IsAffine ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_affine f C ij
  haveI : IsOpenImmersion p :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_isOpenImmersion
      f C ij kl
  have hp : IsIso (BundleSectionZeroLocus.pullbackUnitComparison p) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_pullbackUnitComparison_isIso
      f C ij kl
  have hc : c.hom = A.hom ≫ B.hom := by
    rfl
  have hcanonical :
      SheafOfModules.sectionsMap B.hom
        (BundleSectionZeroLocus.pullbackSection p
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) hp
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C ij)) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalCanonicalSection
        f C ij kl := by
    calc
      SheafOfModules.sectionsMap B.hom
          (BundleSectionZeroLocus.pullbackSection p
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) hp
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C ij)) =
          SheafOfModules.sectionsMap B.hom
            (SheafOfModules.sectionsMap A.hom
              (BundleSectionZeroLocus.restrictModuleSection p
                (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij)
                (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C ij))) := by
          exact congrArg (SheafOfModules.sectionsMap B.hom)
            (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p hp _).symm
      _ = SheafOfModules.sectionsMap (A.hom ≫ B.hom)
            (BundleSectionZeroLocus.restrictModuleSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij)
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C ij)) :=
          (SheafOfModules.sectionsMap_comp A.hom B.hom _).symm
      _ = SheafOfModules.sectionsMap c.hom
            (BundleSectionZeroLocus.restrictModuleSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij)
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C ij)) := by
          exact congrArg (fun g => SheafOfModules.sectionsMap g
            (BundleSectionZeroLocus.restrictModuleSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij)
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C ij))) hc.symm
      _ = SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalCanonicalSection
            f C ij kl := by
          simpa only [SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection,
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalCanonicalSection]
            using SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftRestrictedPullbackSection_toLeftLocal
              f C e.canonicalSection ij kl
  have hlift :
      SheafOfModules.sectionsMap B.hom
        (BundleSectionZeroLocus.pullbackSection p
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) hp
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed ij)) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalLiftSection
        f C seed ij kl := by
    calc
      SheafOfModules.sectionsMap B.hom
          (BundleSectionZeroLocus.pullbackSection p
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) hp
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed ij)) =
          SheafOfModules.sectionsMap B.hom
            (SheafOfModules.sectionsMap A.hom
              (BundleSectionZeroLocus.restrictModuleSection p
                (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij)
                (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed ij))) := by
          exact congrArg (SheafOfModules.sectionsMap B.hom)
            (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p hp _).symm
      _ = SheafOfModules.sectionsMap (A.hom ≫ B.hom)
            (BundleSectionZeroLocus.restrictModuleSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij)
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed ij)) :=
          (SheafOfModules.sectionsMap_comp A.hom B.hom _).symm
      _ = SheafOfModules.sectionsMap c.hom
            (BundleSectionZeroLocus.restrictModuleSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij)
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed ij)) := by
          exact congrArg (fun g => SheafOfModules.sectionsMap g
            (BundleSectionZeroLocus.restrictModuleSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij)
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed ij))) hc.symm
      _ = SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalLiftSection
            f C seed ij kl := by
          simpa only [SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection,
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftLocalLiftSection]
            using SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftRestrictedPullbackSection_toLeftLocal
              f C seed.lift ij kl
  have hsection : SheafOfModules.sectionsMap c.hom sC = sL := by
    calc
      SheafOfModules.sectionsMap c.hom sC =
          SheafOfModules.sectionsMap B.hom
            (SheafOfModules.sectionsMap A.hom sC) := by
          rw [hc]
          exact SheafOfModules.sectionsMap_comp A.hom B.hom sC
      _ = SheafOfModules.sectionsMap B.hom
            (BundleSectionZeroLocus.pullbackSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C ij) hp s) := by
          exact congrArg (SheafOfModules.sectionsMap B.hom)
            (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p hp s)
      _ = sL := by
          dsimp [s, sL]
          unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection
            SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilSection
          rw [BundleSectionZeroLocus.pullbackSection_linearCombination,
            BundleSectionZeroLocus.sectionsMap_addSections,
            BundleSectionZeroLocus.sectionsMap_scaleSection,
            BundleSectionZeroLocus.sectionsMap_scaleSection, hcanonical, hlift]
          rfl
  change (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eLocal s).comap p =
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eL sL
  rw [BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction p
    (ULift.{u} (Fin 2)) eLocal s]
  change BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eC sC =
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eL sL
  calc
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eC sC =
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) (eC ≪≫ c)
        (SheafOfModules.sectionsMap c.hom sC) :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq
        (ULift.{u} (Fin 2)) eC c sC
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) (eC ≪≫ c) sL := by
      rw [hsection]
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eL sL :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso
        (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) (eC ≪≫ c) eL sL

/-- Restricting a normalized local pencil zero ideal to an arbitrary product-chart
overlap gives its right local presentation on that overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_comap_snd
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed kl).comap
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilZeroIdeal
        f C seed ij kl := by
  let p := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let q := SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLocalScheme f C kl
  let E := (AlgebraicGeometry.Scheme.Modules.overEquiv (C.U kl.1)).functor.obj
    (e.E.over (C.U kl.1))
  let A := (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback p).app
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl)
  let B := (AlgebraicGeometry.Scheme.Modules.pullbackComp p q).app E
  let c := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightRestrictionToLocalModuleIso
    f C ij kl
  let eR := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalFreeIso
    f C ij kl
  let sR := SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilSection
    f C seed ij kl
  let eLocal := SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C kl
  let s := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection f C seed kl
  let eC := BundleSectionZeroLocus.restrictionFreeIsoOf p (ULift.{u} (Fin 2)) eLocal
  let sC := BundleSectionZeroLocus.restrictModuleSection p
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) s
  haveI : IsAffine (SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap
      f C ij kl) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_affine f C ij kl
  haveI : IsAffine ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X kl) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_affine f C kl
  haveI : IsOpenImmersion p :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_snd_isOpenImmersion
      f C ij kl
  have hp : IsIso (BundleSectionZeroLocus.pullbackUnitComparison p) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_snd_pullbackUnitComparison_isIso
      f C ij kl
  have hc : c.hom = A.hom ≫ B.hom := by
    rfl
  have hcanonical :
      SheafOfModules.sectionsMap B.hom
        (BundleSectionZeroLocus.pullbackSection p
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) hp
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C kl)) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalCanonicalSection
        f C ij kl := by
    calc
      SheafOfModules.sectionsMap B.hom
          (BundleSectionZeroLocus.pullbackSection p
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) hp
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C kl)) =
          SheafOfModules.sectionsMap B.hom
            (SheafOfModules.sectionsMap A.hom
              (BundleSectionZeroLocus.restrictModuleSection p
                (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl)
                (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C kl))) := by
          exact congrArg (SheafOfModules.sectionsMap B.hom)
            (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p hp _).symm
      _ = SheafOfModules.sectionsMap (A.hom ≫ B.hom)
            (BundleSectionZeroLocus.restrictModuleSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl)
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C kl)) :=
          (SheafOfModules.sectionsMap_comp A.hom B.hom _).symm
      _ = SheafOfModules.sectionsMap c.hom
            (BundleSectionZeroLocus.restrictModuleSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl)
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C kl)) := by
          exact congrArg (fun g => SheafOfModules.sectionsMap g
            (BundleSectionZeroLocus.restrictModuleSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl)
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C kl))) hc.symm
      _ = SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalCanonicalSection
            f C ij kl := by
          simpa only [SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection,
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalCanonicalSection]
            using SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightRestrictedPullbackSection_toRightLocal
              f C e.canonicalSection ij kl
  have hlift :
      SheafOfModules.sectionsMap B.hom
        (BundleSectionZeroLocus.pullbackSection p
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) hp
          (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed kl)) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalLiftSection
        f C seed ij kl := by
    calc
      SheafOfModules.sectionsMap B.hom
          (BundleSectionZeroLocus.pullbackSection p
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) hp
            (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed kl)) =
          SheafOfModules.sectionsMap B.hom
            (SheafOfModules.sectionsMap A.hom
              (BundleSectionZeroLocus.restrictModuleSection p
                (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl)
                (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed kl))) := by
          exact congrArg (SheafOfModules.sectionsMap B.hom)
            (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p hp _).symm
      _ = SheafOfModules.sectionsMap (A.hom ≫ B.hom)
            (BundleSectionZeroLocus.restrictModuleSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl)
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed kl)) :=
          (SheafOfModules.sectionsMap_comp A.hom B.hom _).symm
      _ = SheafOfModules.sectionsMap c.hom
            (BundleSectionZeroLocus.restrictModuleSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl)
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed kl)) := by
          exact congrArg (fun g => SheafOfModules.sectionsMap g
            (BundleSectionZeroLocus.restrictModuleSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl)
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed kl))) hc.symm
      _ = SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalLiftSection
            f C seed ij kl := by
          simpa only [SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection,
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightLocalLiftSection]
            using SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightRestrictedPullbackSection_toRightLocal
              f C seed.lift ij kl
  have hsection : SheafOfModules.sectionsMap c.hom sC = sR := by
    calc
      SheafOfModules.sectionsMap c.hom sC =
          SheafOfModules.sectionsMap B.hom
            (SheafOfModules.sectionsMap A.hom sC) := by
          rw [hc]
          exact SheafOfModules.sectionsMap_comp A.hom B.hom sC
      _ = SheafOfModules.sectionsMap B.hom
            (BundleSectionZeroLocus.pullbackSection p
              (SerreExtensionRankTwoAffineCover.projectiveLineLocalModule f C kl) hp s) := by
          exact congrArg (SheafOfModules.sectionsMap B.hom)
            (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p hp s)
      _ = sR := by
          dsimp [s, sR]
          unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection
            SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
            SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilSection
          rw [BundleSectionZeroLocus.pullbackSection_linearCombination,
            BundleSectionZeroLocus.sectionsMap_addSections,
            BundleSectionZeroLocus.sectionsMap_scaleSection,
            BundleSectionZeroLocus.sectionsMap_scaleSection, hcanonical, hlift]
          rfl
  change (BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eLocal s).comap p =
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eR sR
  rw [BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction p
    (ULift.{u} (Fin 2)) eLocal s]
  change BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eC sC =
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eR sR
  calc
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eC sC =
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) (eC ≪≫ c)
        (SheafOfModules.sectionsMap c.hom sC) :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq
        (ULift.{u} (Fin 2)) eC c sC
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) (eC ≪≫ c) sR := by
      rw [hsection]
    _ = BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) eR sR :=
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso
        (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) (eC ≪≫ c) eR sR

/-- The normalized local zero ideals satisfy the full cocycle condition on every
pair of affine product charts of the projective-line parameter space. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_comap_overlap
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).comap
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) =
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed kl).comap
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) := by
  calc
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).comap
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) =
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapLeftNormalizedPencilZeroIdeal
        f C seed ij kl :=
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_comap_fst
        f C seed ij kl
    _ = SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlapRightNormalizedPencilZeroIdeal
        f C seed ij kl :=
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_normalizedPencilZeroIdeal_eq_all
        f C seed ij kl
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed kl).comap
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) :=
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_comap_snd
        f C seed ij kl).symm

/-- Reindexing a pulled-back ideal subscheme along an isomorphism of the
ambient source schemes.  This is the scheme-theoretic counterpart of
reindexing an ordinary intersection of open sets, and will identify the two
orders of a product-chart overlap. -/
noncomputable def reindexComapSubschemeIsoOfIso
    {U V W : Scheme.{u}} (I : W.IdealSheafData) (r : U ≅ V)
    (a : U ⟶ W) (b : V ⟶ W) (hr : r.hom ≫ b = a) :
    (I.comap a).subscheme ≅ (I.comap b).subscheme := by
  have hcomap : I.comap a = (I.comap b).comap r.hom := by
    rw [← Scheme.IdealSheafData.comap_comp, hr]
  exact eqToIso (congrArg Scheme.IdealSheafData.subscheme hcomap) ≪≫
    (I.comap b).comapIso r.hom ≪≫ asIso (pullback.snd r.hom (I.comap b).subschemeι)

/-- The reindexing isomorphism preserves the canonical map to the original
closed subscheme. -/
theorem reindexComapSubschemeIsoOfIso_hom_comp_comapSubschemeι
    {U V W : Scheme.{u}} (I : W.IdealSheafData) (r : U ≅ V)
    (a : U ⟶ W) (b : V ⟶ W) (hr : r.hom ≫ b = a) :
    (reindexComapSubschemeIsoOfIso I r a b hr).hom ≫
        (I.comapIso b).hom ≫ pullback.snd b I.subschemeι =
      (I.comapIso a).hom ≫ pullback.snd a I.subschemeι := by
  apply (cancel_mono I.subschemeι).mp
  unfold reindexComapSubschemeIsoOfIso
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← pullback.condition (f := b) (g := I.subschemeι)]
  rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  rw [← pullback.condition_assoc (f := r.hom) (g := (I.comap b).subschemeι) (h := b)]
  rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  rw [← Category.assoc]
  rw [idealSheafData_eqToIso_subschemeι]
  · rw [hr]
    rw [← pullback.condition (f := a) (g := I.subschemeι)]
    rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  · rw [← Scheme.IdealSheafData.comap_comp, hr]

/-- Transporting an equality of ideal data into a pulled-back closed
subscheme preserves the canonical map to the ambient target. -/
theorem eqToIso_comapSubschemeMap_to_ambient
    {A B : Scheme.{u}} (I : A.IdealSheafData) (J : B.IdealSheafData)
    (f : A ⟶ B) (h : I = J.comap f) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫
        (J.comapIso f).hom ≫ pullback.snd f J.subschemeι ≫ J.subschemeι =
      I.subschemeι ≫ f := by
  rw [comapSubschemeMap_to_ambient]
  rw [← Category.assoc]
  rw [idealSheafData_eqToIso_subschemeι I (J.comap f) h]

/-- A closed subscheme described by an ideal equal to a pullback is the
corresponding categorical pullback, also when its presentation is transported
along that equality. -/
theorem isPullback_eqToIso_comapSubschemeMap
    {A B : Scheme.{u}} (I : A.IdealSheafData) (J : B.IdealSheafData)
    (f : A ⟶ B) (h : I = J.comap f) :
    IsPullback I.subschemeι
      ((eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫
        (J.comapIso f).hom ≫ pullback.snd f J.subschemeι)
      f J.subschemeι := by
  apply AlgebraicGeometry.isPullback_of_isClosedImmersion
  · simpa only [Category.assoc] using
      (eqToIso_comapSubschemeMap_to_ambient I J f h).symm
  · rw [Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι]
    exact h.symm

/-- The left presentation of the zero locus on the intersection of two
affine product charts. -/
noncomputable abbrev
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    Scheme.{u} :=
  ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij).comap
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).subscheme

/-- The right presentation of the same product-chart zero-locus overlap. -/
noncomputable abbrev
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRight
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    Scheme.{u} :=
  ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed kl).comap
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).subscheme

/-- The canonical open inclusion of an overlap zero locus into its left
local zero locus. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
      f C seed ij kl ⟶
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subscheme :=
  (((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij).comapIso
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).hom ≫
    pullback.snd _
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι)

/-- The overlap inclusion into the left local zero locus is open. -/
theorem
    SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroOverlapι
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
  letI : IsOpenImmersion
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_isOpenImmersion
      f C ij kl
  letI : IsOpenImmersion
      (pullback.snd
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed ij).subschemeι) := inferInstance
  infer_instance

/-- Equality of the normalized equations induces the transition from the
left to the right overlap presentation. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapIso
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
      f C seed ij kl ≅
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRight
        f C seed ij kl :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_comap_overlap
      f C seed ij kl))

/-- Reindex the right overlap presentation along symmetry of the ambient
pullback, obtaining the left presentation with the two product charts
reversed. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapReindexIso
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRight
      f C seed ij kl ≅
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
        f C seed kl ij := by
  apply reindexComapSubschemeIsoOfIso
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed kl)
    (pullbackSymmetry
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
  exact pullbackSymmetry_hom_comp_fst _ _

/-- Ambient-pullback symmetry preserves the canonical map from the right
overlap presentation to the local zero locus on the right chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapReindexIso_hom_comp_ι
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapReindexIso
      f C seed ij kl).hom ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed kl ij =
    ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed kl).comapIso
        (pullback.snd
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).hom ≫
      pullback.snd _
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed kl).subschemeι := by
  exact reindexComapSubschemeIsoOfIso_hom_comp_comapSubschemeι
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed kl)
    (pullbackSymmetry
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
    (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
    (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij))
    (pullbackSymmetry_hom_comp_fst _ _)

/-- The canonical transition from the overlap on one product chart to the
same overlap on the other product chart. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
      f C seed ij kl ≅
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
        f C seed kl ij :=
  SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapIso
    f C seed ij kl ≪≫
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapReindexIso
      f C seed ij kl

/-- The map from an overlap to the local zero locus on its right chart. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
      f C seed ij kl ⟶
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed kl).subscheme :=
  (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
    f C seed ij kl).hom ≫
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed kl ij

/-- The transition followed by the reversed left inclusion is the right
overlap map by construction. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_left_eq_rightMap
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
      f C seed ij kl).hom ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed kl ij =
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
      f C seed ij kl := rfl

/-- The map from an overlap into its right local zero locus is open. -/
theorem
    SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroOverlapRightMap
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed ij kl) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
  letI : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
        f C seed ij kl).hom := by
    apply IsOpenImmersion.of_isIso
  letI : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed kl ij) :=
    SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed kl ij
  infer_instance

instance SerreExtensionRankTwoAffineCover.mono_projectiveLineNormalizedLocalPencilZeroOverlapι
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    Mono (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed ij kl) :=
  (SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroOverlapι
    f C seed ij kl).mono

/-- The pairwise overlap inclusion commutes with the two closed immersions
into its ambient product chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι_comp_subschemeι
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι =
    ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).comap
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).subschemeι ≫
      pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

/-- The pairwise overlap zero locus is the pullback of the local closed zero
locus along the corresponding ambient-chart overlap map. -/
theorem
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroOverlap
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsPullback
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).comap
          (pullback.fst
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).subschemeι
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl)
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι := by
  apply AlgebraicGeometry.isPullback_of_isClosedImmersion
  · exact (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι_comp_subschemeι
      f C seed ij kl).symm
  · rw [Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι]

/-- The ambient triple intersection of the `ij`, `kl`, and `mn` product
charts, parenthesized through the first chart. -/
noncomputable abbrev
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbient
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    Scheme.{u} :=
  pullback
    (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
    (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn))

/-- The triple zero-locus restriction, formed by successively restricting
the normalized ideal on the first chart through the `ij,kl` overlap and then
through the third chart. -/
noncomputable abbrev
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlap
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    Scheme.{u} :=
  (((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij).comap
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).comap
      (pullback.fst
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)))).subscheme

/-- Restriction from the triple zero locus to the `ij,kl` pairwise zero
locus. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlap
      f C seed ij kl mn ⟶
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
        f C seed ij kl :=
  (((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij).comap
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).comapIso
      (pullback.fst
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)))).hom ≫
    pullback.snd _ _

/-- The same triple zero locus mapped to the `ij,mn` pairwise zero locus.
The source is transported using equality of the two successive pullbacks of
the first-chart ideal. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlap
      f C seed ij kl mn ⟶
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
        f C seed ij mn := by
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  let a₁ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₂ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let b₁ := pullback.fst a₁ a₂
  let b₂ := pullback.snd a₁ a₂
  have h : (I.comap a₁).comap b₁ = (I.comap a₂).comap b₂ := by
    rw [← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, pullback.condition]
  exact (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫
    ((I.comap a₂).comapIso b₂).hom ≫ pullback.snd _ _

/-- The first triple-restriction map is open. -/
theorem
    SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroTripleOverlapι
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn) := by
  let a₁ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₂ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let b₁ := pullback.fst a₁ a₂
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  change IsOpenImmersion (((I.comap a₁).comapIso b₁).hom ≫
    pullback.snd b₁ (I.comap a₁).subschemeι)
  letI : IsOpenImmersion a₂ :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_isOpenImmersion
      f C ij mn
  letI : IsOpenImmersion b₁ := by infer_instance
  letI : IsOpenImmersion (pullback.snd b₁ (I.comap a₁).subschemeι) := inferInstance
  infer_instance

/-- The second triple-restriction map is open. -/
theorem
    SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
        f C seed ij kl mn) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
  let a₁ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₂ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let b₂ := pullback.snd a₁ a₂
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  letI : IsOpenImmersion a₁ :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCoverGeneralOverlap_fst_isOpenImmersion
      f C ij kl
  letI : IsOpenImmersion b₂ := by infer_instance
  letI : IsOpenImmersion (pullback.snd b₂ (I.comap a₂).subschemeι) := inferInstance
  have h : (I.comap a₁).comap (pullback.fst a₁ a₂) =
      (I.comap a₂).comap b₂ := by
    rw [← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, pullback.condition]
  change IsOpenImmersion
    ((eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫
      ((I.comap a₂).comapIso b₂).hom ≫ pullback.snd b₂ (I.comap a₂).subschemeι)
  letI : IsOpenImmersion
      (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom := by
    apply IsOpenImmersion.of_isIso
  infer_instance

/-- The first triple restriction commutes with the closed immersions into
the pairwise ambient overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι_comp_subschemeι
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn ≫
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).comap
          (pullback.fst
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).subschemeι =
    (((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).comap
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).comap
        (pullback.fst
          (pullback.fst
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
          (pullback.fst
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)))).subschemeι ≫
      pullback.fst
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlap
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

/-- The closed immersion of a pairwise zero locus into its ambient product-chart
intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
      f C seed ij kl ⟶
      pullback
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) :=
  ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij).comap
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).subschemeι

/-- The closed immersion of a triple zero locus into its ambient triple
product-chart intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlap
      f C seed ij kl mn ⟶
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbient
        f C ij kl mn :=
  (((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij).comap
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).comap
      (pullback.fst
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)))).subschemeι

/-- The right map from a pairwise overlap factors through the right ambient
projection from the product-chart intersection. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_comp_subschemeι
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed ij kl ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed kl).subschemeι =
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
      f C seed ij kl ≫
      pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapReindexIso
      f C seed ij kl).hom
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed kl ij)
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed kl).subschemeι]
  rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapReindexIso_hom_comp_ι]
  simp only [Category.assoc]
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapIso
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
  exact eqToIso_comapSubschemeMap_to_ambient
    ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).comap
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)))
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed kl)
    (pullback.snd
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_comap_overlap
      f C seed ij kl)

/-- The ambient restriction from the triple product-chart intersection to the
`ij,mn` pairwise intersection. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToIk
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbient
      f C ij kl mn ⟶
      pullback
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn) :=
  pullback.snd
    (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
    (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn))

/-- The two paths from the triple product-chart intersection to the first
chart induce the same restricted normalized ideal. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleIdeal_eq_toOverlapIk
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).comap
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).comap
      (pullback.fst
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn))) =
    ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).comap
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn))).comap
      (pullback.snd
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn))) := by
  rw [← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, pullback.condition]

/-- The second triple restriction is the pullback of the `ij,mn` pairwise
closed zero locus along the ambient restriction. -/
theorem
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsPullback
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
        f C seed ij kl mn)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
        f C seed ij kl mn)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToIk
        f C ij kl mn)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
        f C seed ij mn) := by
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  let a₁ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₂ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let b₁ := pullback.fst a₁ a₂
  let b₂ := pullback.snd a₁ a₂
  have h : (I.comap a₁).comap b₁ = (I.comap a₂).comap b₂ := by
    exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleIdeal_eq_toOverlapIk
      f C seed ij kl mn
  simpa only [
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι,
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk,
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToIk,
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι]
    using isPullback_eqToIso_comapSubschemeMap ((I.comap a₁).comap b₁)
      (I.comap a₂) b₂ h

/-- The first triple restriction is the pullback of the pairwise closed
zero locus along the ambient third-chart restriction. -/
theorem
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlap
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsPullback
      (((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).comap
          (pullback.fst
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).comap
          (pullback.fst
            (pullback.fst
              ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
              ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
            (pullback.fst
              ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
              ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)))).subschemeι
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn)
      (pullback.fst
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)))
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).comap
          (pullback.fst
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
            ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).subschemeι := by
  apply AlgebraicGeometry.isPullback_of_isClosedImmersion
  · exact
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι_comp_subschemeι
        f C seed ij kl mn).symm
  · rw [Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι]

/-- The two triple restrictions agree after mapping into the normalized local
zero locus on the first product chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToLeft_eq_toIk
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl =
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij mn := by
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  let a₁ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₂ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let b₁ := pullback.fst a₁ a₂
  let b₂ := pullback.snd a₁ a₂
  let Htriple :=
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlap
      f C seed ij kl mn
  let HtoIk :=
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
      f C seed ij kl mn
  apply (cancel_mono I.subschemeι).mp
  calc
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl) ≫ I.subschemeι =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
          f C seed ij kl ≫ I.subschemeι) := by simp only [Category.assoc]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
          f C seed ij kl mn ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed ij kl ≫ a₁) := by
      unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
      rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι_comp_subschemeι]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed ij kl) ≫ a₁ := by simp only [Category.assoc]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫ b₁) ≫ a₁ := by
      unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
      rw [Htriple.w]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫ (b₁ ≫ a₁) := by simp only [Category.assoc]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫ (b₂ ≫ a₂) := by
      rw [pullback.condition]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToIk
          f C ij kl mn) ≫ a₂ := by rfl
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed ij mn) ≫ a₂ := by
      rw [HtoIk.w]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
          f C seed ij kl mn ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed ij mn ≫ a₂) := by simp only [Category.assoc]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
          f C seed ij kl mn ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
          f C seed ij mn ≫ I.subschemeι) := by
      unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
      rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι_comp_subschemeι]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
          f C seed ij mn) ≫ I.subschemeι := by simp only [Category.assoc]

/-- The triple zero locus is the categorical pullback of its two pairwise
restrictions to the `ij,kl` and `ij,mn` product-chart intersections. -/
theorem
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlap_pairwise
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsPullback
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
        f C seed ij kl mn)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij mn) := by
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  let a₁ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₂ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let b₁ := pullback.fst a₁ a₂
  let b₂ := pullback.snd a₁ a₂
  let Hambient := IsPullback.of_hasPullback a₁ a₂
  let Hij :=
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroOverlap
      f C seed ij kl
  let Himn :=
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroOverlap
      f C seed ij mn
  let Htriple :=
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlap
      f C seed ij kl mn
  let HtoIk :=
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
      f C seed ij kl mn
  have hcone :
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
          f C seed ij kl =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
          f C seed ij mn :=
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToLeft_eq_toIk
      f C seed ij kl mn
  let q : ∀ s : PullbackCone
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij mn),
      s.pt ⟶ pullback a₁ a₂ := fun s =>
    Hambient.lift (s.fst ≫ (I.comap a₁).subschemeι)
      (s.snd ≫ (I.comap a₂).subschemeι) (by
        calc
          (s.fst ≫ (I.comap a₁).subschemeι) ≫ a₁ =
              s.fst ≫ ((I.comap a₁).subschemeι ≫ a₁) := by
                simp only [Category.assoc]
          _ = s.fst ≫
              (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
                f C seed ij kl ≫ I.subschemeι) := by rw [Hij.w]
          _ = (s.fst ≫
              SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
                f C seed ij kl) ≫ I.subschemeι := by
                simp only [Category.assoc]
          _ = (s.snd ≫
              SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
                f C seed ij mn) ≫ I.subschemeι := by rw [s.condition]
          _ = s.snd ≫
              (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
                f C seed ij mn ≫ I.subschemeι) := by
                simp only [Category.assoc]
          _ = s.snd ≫ ((I.comap a₂).subschemeι ≫ a₂) := by rw [Himn.w]
          _ = (s.snd ≫ (I.comap a₂).subschemeι) ≫ a₂ := by
                simp only [Category.assoc])
  let lift : ∀ s : PullbackCone
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij mn),
      s.pt ⟶ SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlap
        f C seed ij kl mn := fun s =>
    Htriple.lift (q s) s.fst (by
      dsimp [q]
      exact Hambient.lift_fst _ _ _)
  have lift_fst (s : PullbackCone
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij mn)) :
      lift s ≫ SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn = s.fst := by
    dsimp [lift]
    exact Htriple.lift_snd _ _ _
  let _ : Mono
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij mn) :=
    (SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed ij mn).mono
  have lift_snd (s : PullbackCone
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij mn)) :
      lift s ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
          f C seed ij kl mn = s.snd := by
    apply (cancel_mono
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij mn)).mp
    rw [Category.assoc, ← hcone, ← Category.assoc, lift_fst, s.condition]
  refine ⟨⟨hcone⟩, ⟨PullbackCone.isLimitAux
    (PullbackCone.mk
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
        f C seed ij kl mn)
      hcone) lift (fun s => lift_fst s) (fun s => lift_snd s) ?_⟩⟩
  intro s m hm
  change s.pt ⟶ SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlap
    f C seed ij kl mn at m
  have hm_fst : m ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn = s.fst := by
    have h := hm WalkingCospan.left
    change m ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
          f C seed ij kl mn = s.fst at h
    exact h
  have hm_snd : m ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
        f C seed ij kl mn = s.snd := by
    have h := hm WalkingCospan.right
    change m ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
          f C seed ij kl mn = s.snd at h
    exact h
  apply Htriple.hom_ext
  · have hlift_ambient : lift s ≫ ((I.comap a₁).comap b₁).subschemeι = q s := by
      dsimp [lift]
      exact Htriple.lift_fst _ _ _
    apply Hambient.hom_ext
    · rw [hlift_ambient]
      change m ≫ ((I.comap a₁).comap b₁).subschemeι ≫ b₁ = q s ≫ b₁
      calc
        m ≫ ((I.comap a₁).comap b₁).subschemeι ≫ b₁ =
            m ≫
              (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
                f C seed ij kl mn ≫ (I.comap a₁).subschemeι) := by
              rw [Htriple.w]
        _ = s.fst ≫ (I.comap a₁).subschemeι := by
              rw [← Category.assoc, hm_fst]
        _ = q s ≫ b₁ := by
              dsimp [q]
              exact (Hambient.lift_fst _ _ _).symm
    · rw [hlift_ambient]
      change m ≫
          SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
            f C seed ij kl mn ≫
          SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToIk
            f C ij kl mn = q s ≫ b₂
      calc
        m ≫
            SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
              f C seed ij kl mn ≫
            SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToIk
              f C ij kl mn =
            m ≫
              (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
                f C seed ij kl mn ≫
              SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
                f C seed ij mn) := by rw [HtoIk.w]
        _ = s.snd ≫ (I.comap a₂).subschemeι := by
              unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
              rw [← Category.assoc, hm_snd]
        _ = q s ≫ b₂ := by
              dsimp [q]
              exact (Hambient.lift_snd _ _ _).symm
  · rw [hm_fst, lift_fst]

/-- The ambient triple intersection maps to the pairwise intersection of the
second and third product charts. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbient
      f C ij kl mn ⟶
      pullback
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn) := by
  let a₁ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₂ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let b₁ := pullback.fst a₁ a₂
  let b₂ := pullback.snd a₁ a₂
  let r₁ := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let r₂ := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  exact pullback.lift (b₁ ≫ r₁) (b₂ ≫ r₂) (by
    calc
      (b₁ ≫ r₁) ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl =
          b₁ ≫ (r₁ ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) := by
            simp only [Category.assoc]
      _ = b₁ ≫ (a₁ ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) := by
            rw [pullback.condition]
      _ = (b₁ ≫ a₁) ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij := by
            simp only [Category.assoc]
      _ = (b₂ ≫ a₂) ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij := by
            rw [pullback.condition]
      _ = b₂ ≫ (a₂ ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) := by
            simp only [Category.assoc]
      _ = b₂ ≫ (r₂ ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn) := by
            rw [pullback.condition]
      _ = (b₂ ≫ r₂) ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn := by
            simp only [Category.assoc])

/-- The first projection of the ambient `jk` triple restriction. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk_fst
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk
        f C ij kl mn ≫
      pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn) =
    pullback.fst
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)) ≫
      pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk
  exact pullback.lift_fst _ _ _

/-- The second projection of the ambient `jk` triple restriction. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk_snd
    (C : SerreExtensionRankTwoAffineCover e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk
        f C ij kl mn ≫
      pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn) =
    pullback.snd
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)) ≫
      pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk
  exact pullback.lift_snd _ _ _

/-- The normalized ideal on the triple product-chart intersection agrees with
the pullback of the `kl,mn` overlap ideal along the ambient `jk` restriction. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleIdeal_eq_toOverlapJk
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).comap
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))).comap
      (pullback.fst
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl))
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn))) =
    ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed kl).comap
        (pullback.fst
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn))).comap
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk
        f C ij kl mn) := by
  let Iij := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  let Ikl := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed kl
  let a₁ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₂ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let b₁ := pullback.fst a₁ a₂
  let r₁ := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let r₂ := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let a₃ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let δ := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk
    f C ij kl mn
  change (Iij.comap a₁).comap b₁ = (Ikl.comap a₃).comap δ
  calc
    (Iij.comap a₁).comap b₁ = (Ikl.comap r₁).comap b₁ := by
      exact congrArg (fun L => L.comap b₁)
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_comap_overlap
          f C seed ij kl)
    _ = Ikl.comap (b₁ ≫ r₁) := by
      rw [← Scheme.IdealSheafData.comap_comp]
    _ = Ikl.comap (δ ≫ a₃) := by
      rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk_fst]
    _ = (Ikl.comap a₃).comap δ := by
      rw [← Scheme.IdealSheafData.comap_comp]

/-- The common triple zero locus restricted to the `kl,mn` pairwise zero
locus.  The map is induced by the equality between its first-chart ideal
presentation and the pullback of the `kl,mn` presentation. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlap
      f C seed ij kl mn ⟶
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
        f C seed kl mn := by
  let Iij := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  let Ikl := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed kl
  let a₁ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₂ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let b₁ := pullback.fst a₁ a₂
  let a₃ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let δ := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk
    f C ij kl mn
  have h : (Iij.comap a₁).comap b₁ = (Ikl.comap a₃).comap δ := by
    exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleIdeal_eq_toOverlapJk
      f C seed ij kl mn
  exact (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫
    ((Ikl.comap a₃).comapIso δ).hom ≫ pullback.snd δ (Ikl.comap a₃).subschemeι

/-- The `jk` triple restriction is the closed-subscheme base change of the
`kl,mn` pairwise zero locus along the ambient third-intersection map. -/
theorem
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsPullback
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
        f C seed ij kl mn)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
        f C seed ij kl mn)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk
        f C ij kl mn)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
        f C seed kl mn) := by
  let Iij := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  let Ikl := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed kl
  let a₁ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₂ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let b₁ := pullback.fst a₁ a₂
  let a₃ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let δ := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk
    f C ij kl mn
  have h : (Iij.comap a₁).comap b₁ = (Ikl.comap a₃).comap δ := by
    exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleIdeal_eq_toOverlapJk
      f C seed ij kl mn
  change IsPullback ((Iij.comap a₁).comap b₁).subschemeι
    ((eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫
      ((Ikl.comap a₃).comapIso δ).hom ≫ pullback.snd δ (Ikl.comap a₃).subschemeι)
    δ (Ikl.comap a₃).subschemeι
  exact isPullback_eqToIso_comapSubschemeMap ((Iij.comap a₁).comap b₁)
    (Ikl.comap a₃) δ h

/-- Restricting the triple overlap to the `kl,mn` overlap agrees with first
restricting to `ij,kl` and then taking that overlap's right local map. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk_comp_ι
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed kl mn =
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed ij kl := by
  let Ikl := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed kl
  let a₁ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₂ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let b₁ := pullback.fst a₁ a₂
  let r₁ := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₃ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let δ := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk
    f C ij kl mn
  let Htriple :=
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlap
      f C seed ij kl mn
  let HtoJk :=
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
      f C seed ij kl mn
  apply (cancel_mono Ikl.subschemeι).mp
  calc
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed kl mn) ≫ Ikl.subschemeι =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
        f C seed ij kl mn ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
          f C seed kl mn ≫ Ikl.subschemeι) := by
            simp only [Category.assoc]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
          f C seed ij kl mn ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed kl mn ≫ a₃) := by
            unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
            rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι_comp_subschemeι]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed kl mn) ≫ a₃ := by
            simp only [Category.assoc]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫ δ) ≫ a₃ := by
            rw [HtoJk.w]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫ (δ ≫ a₃) := by
            simp only [Category.assoc]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫ (b₁ ≫ r₁) := by
            rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk_fst]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫ b₁) ≫ r₁ := by
            simp only [Category.assoc]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed ij kl) ≫ r₁ := by
            unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
              SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
            rw [Htriple.w]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
          f C seed ij kl mn ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed ij kl ≫ r₁) := by
            simp only [Category.assoc]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
          f C seed ij kl mn ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed ij kl ≫ Ikl.subschemeι) := by
            rw [← SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_comp_subschemeι]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed ij kl) ≫ Ikl.subschemeι := by
            simp only [Category.assoc]

/-- The `jk` and `ik` routes from the common triple restriction induce the
same map to the local zero locus on the third product chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk_comp_rightMap
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed kl mn =
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed ij mn := by
  let Imn := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed mn
  let a₁ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let a₂ := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let b₂ := pullback.snd a₁ a₂
  let r₂ := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let r₃ := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f mn)
  let δ := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk
    f C ij kl mn
  let HtoIk :=
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
      f C seed ij kl mn
  let HtoJk :=
    SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
      f C seed ij kl mn
  apply (cancel_mono Imn.subschemeι).mp
  calc
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed kl mn) ≫ Imn.subschemeι =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
        f C seed ij kl mn ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed kl mn ≫ Imn.subschemeι) := by
            simp only [Category.assoc]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
          f C seed ij kl mn ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed kl mn ≫ r₃) := by
            rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_comp_subschemeι]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed kl mn) ≫ r₃ := by
            simp only [Category.assoc]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫ δ) ≫ r₃ := by
            rw [HtoJk.w]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫ (δ ≫ r₃) := by
            simp only [Category.assoc]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫ (b₂ ≫ r₂) := by
            rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToJk_snd]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫ b₂) ≫ r₂ := by
            simp only [Category.assoc]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapSubschemeι
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleAmbientToIk
          f C ij kl mn) ≫ r₂ := by
            rfl
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed ij mn) ≫ r₂ := by
            rw [HtoIk.w]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
          f C seed ij kl mn ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed ij mn ≫ r₂) := by
            simp only [Category.assoc]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
          f C seed ij kl mn ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed ij mn ≫ Imn.subschemeι) := by
            rw [← SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_comp_subschemeι]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
          f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed ij mn) ≫ Imn.subschemeι := by
            simp only [Category.assoc]

/-- The explicit triple zero locus is canonically isomorphic to the
categorical pullback of its `ij,kl` and `ij,mn` pairwise restrictions. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapPairwiseIso
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlap
      f C seed ij kl mn ≅
      pullback
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
          f C seed ij kl)
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
          f C seed ij mn) :=
  (SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlap_pairwise
    f C seed ij kl mn).isoPullback

/-- The first projection of the pairwise-pullback model is the ordinary
restriction to the `ij,kl` overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapPairwiseIso_hom_fst
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapPairwiseIso
      f C seed ij kl mn).hom ≫
        pullback.fst
          (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
            f C seed ij kl)
          (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
            f C seed ij mn) =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn :=
  (SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlap_pairwise
    f C seed ij kl mn).isoPullback_hom_fst

/-- The second projection of the pairwise-pullback model is the alternate
restriction to the `ij,mn` overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapPairwiseIso_hom_snd
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapPairwiseIso
      f C seed ij kl mn).hom ≫
        pullback.snd
          (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
            f C seed ij kl)
          (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
            f C seed ij mn) =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
        f C seed ij kl mn :=
  (SerreExtensionRankTwoAffineCover.isPullback_projectiveLineNormalizedLocalPencilZeroTripleOverlap_pairwise
    f C seed ij kl mn).isoPullback_hom_snd

/-- The crossing map from the pullback of the `ij,kl` and `ij,mn` overlaps
to the `kl,mn` overlap, obtained from the common triple restriction. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    pullback
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij mn) ⟶
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
        f C seed kl mn :=
  (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapPairwiseIso
    f C seed ij kl mn).inv ≫
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk
      f C seed ij kl mn

/-- After restricting to the `kl,mn` overlap, the crossing is the right map
out of the first pairwise overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross_fac
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed kl mn =
    pullback.fst
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij mn) ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed ij kl := by
  let E := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapPairwiseIso
    f C seed ij kl mn
  calc
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed kl mn =
      E.inv ≫ (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
        f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed ij kl) := by
            unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross
            rw [Category.assoc,
              SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk_comp_ι]
    _ = (E.inv ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapι
          f C seed ij kl mn) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed ij kl := by
            simp only [Category.assoc]
    _ = pullback.fst
          (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
            f C seed ij kl)
          (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
            f C seed ij mn) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed ij kl := by
            rw [← SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapPairwiseIso_hom_fst]
            simp [E]

/-- The crossing is also compatible with the right map out of the second
pairwise overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross_right
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl mn : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed kl mn =
    pullback.snd
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij mn) ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed ij mn := by
  let E := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapPairwiseIso
    f C seed ij kl mn
  calc
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross
        f C seed ij kl mn ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed kl mn =
      E.inv ≫ (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
        f C seed ij kl mn ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed ij mn) := by
            unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross
            rw [Category.assoc,
              SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToJk_comp_rightMap]
    _ = (E.inv ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapToIk
          f C seed ij kl mn) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed ij mn := by
            simp only [Category.assoc]
    _ = pullback.snd
          (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
            f C seed ij kl)
          (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
            f C seed ij mn) ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed ij mn := by
            rw [← SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapPairwiseIso_hom_snd]
            simp [E]

/-- The right map of a pairwise overlap is compatible with the two product
chart maps to the parameter space. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_comp_subschemeι_comp_chart
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed ij kl ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed kl).subschemeι ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl =
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij := by
  let a := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let b := pullback.snd
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  calc
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed ij kl ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed kl).subschemeι ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl =
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
        f C seed ij kl ≫ b) ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl := by
        rw [← Category.assoc
          (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
            f C seed ij kl)
          (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
            f C seed kl).subschemeι
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)]
        rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_comp_subschemeι]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed ij kl ≫
        (b ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) := by
          simp only [Category.assoc]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed ij kl ≫
        (a ≫ (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) := by
          rw [pullback.condition]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed ij kl ≫ a) ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij := by
          simp only [Category.assoc]
    _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
          f C seed ij kl ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed ij).subschemeι) ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij := by
          unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          rw [← SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι_comp_subschemeι]

/-- Swapping an overlap and then using the reversed right map recovers its
ordinary left restriction. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_rightMap
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
      f C seed ij kl).hom ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed kl ij =
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed ij kl := by
  apply (cancel_mono
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subschemeι).mp
  apply (cancel_mono
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)).mp
  simp only [Category.assoc]
  calc
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
      f C seed ij kl).hom ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed kl ij ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed ij).subschemeι ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij =
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
        f C seed ij kl).hom ≫
        SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
          f C seed kl ij ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed kl).subschemeι ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl := by
          rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_comp_subschemeι_comp_chart]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
          f C seed ij kl ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed kl).subschemeι ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl := by
          rw [← Category.assoc
            (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
              f C seed ij kl).hom]
          rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_left_eq_rightMap]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
          f C seed ij kl ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed ij).subschemeι ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij := by
          rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_comp_subschemeι_comp_chart]

/-- The two overlap swaps are mutually inverse. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_swap_hom
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
      f C seed ij kl).hom ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
        f C seed kl ij).hom =
      𝟙 _ := by
  apply (cancel_mono
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed ij kl)).mp
  simp only [Category.assoc]
  rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_left_eq_rightMap]
  rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_rightMap]
  simp

/-- Restriction to the self-overlap of a product chart is an isomorphism. -/
theorem
    SerreExtensionRankTwoAffineCover.isIso_projectiveLineNormalizedLocalPencilZeroOverlapι_self
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsIso (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed ij ij) := by
  let g := (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij
  let a := pullback.fst g g
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  change IsIso ((I.comapIso a).hom ≫ pullback.snd a I.subschemeι)
  letI : IsOpenImmersion g :=
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).map_prop _
  letI : IsIso a := by infer_instance
  infer_instance

/-- The diagonal pairwise-overlap map is available as an instance for the
categorical gluing construction. -/
instance
    SerreExtensionRankTwoAffineCover.isIso_projectiveLineNormalizedLocalPencilZeroOverlapι_self_instance
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsIso (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed ij ij) :=
  SerreExtensionRankTwoAffineCover.isIso_projectiveLineNormalizedLocalPencilZeroOverlapι_self
    f C seed ij

/-- On a self-overlap, the right local map equals the ordinary restriction. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_self
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed ij ij =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij ij := by
  let g := (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij
  let a := pullback.fst g g
  let b := pullback.snd g g
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  have hba : b = a := by
    apply (cancel_mono g).mp
    exact pullback.condition.symm
  apply (cancel_mono I.subschemeι).mp
  calc
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed ij ij ≫ I.subschemeι =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
        f C seed ij ij ≫ b := by
          exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_comp_subschemeι
            f C seed ij ij
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          f C seed ij ij ≫ a := by
          rw [hba]
    _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
          f C seed ij ij ≫ I.subschemeι := by
          unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSubschemeι
          rw [← SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι_comp_subschemeι]

/-- The overlap swap is the identity on a self-overlap. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_self
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
      f C seed ij ij).hom =
      𝟙 _ := by
  apply (cancel_mono
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed ij ij)).mp
  rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_left_eq_rightMap,
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_self]
  simp

/-- The normalized local zero loci on the affine product charts of the
projective-line pencil, together with their proved pairwise and triple
overlap maps, form categorical gluing data. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGlueData
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) :
    GlueData Scheme :=
  AllCharacteristics.OverlapComposition.glueData
    (fun ij => (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subscheme)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
      f C seed ij kl)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed ij kl)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
      f C seed ij kl)
    (fun ij kl => (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
      f C seed ij kl).hom)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_left_eq_rightMap
      f C seed ij kl)
    (fun ij kl mn => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross
      f C seed ij kl mn)
    (fun ij kl mn => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross_fac
      f C seed ij kl mn)
    (fun ij kl mn => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross_right
      f C seed ij kl mn)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_swap_hom
      f C seed ij kl)
    (fun ij => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_self
      f C seed ij)

/-- The categorical product-chart overlap datum is a scheme gluing datum,
because every left overlap map is an open immersion. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroSchemeGlueData
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) :
    Scheme.GlueData :=
  AllCharacteristics.OverlapComposition.schemeGlueData
      (fun ij => (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subscheme)
      (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
        f C seed ij kl)
      (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl)
      (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
        f C seed ij kl)
      (fun ij kl => (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
        f C seed ij kl).hom)
      (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_left_eq_rightMap
        f C seed ij kl)
      (fun ij kl mn => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross
        f C seed ij kl mn)
      (fun ij kl mn => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross_fac
        f C seed ij kl mn)
      (fun ij kl mn => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross_right
        f C seed ij kl mn)
      (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_swap_hom
        f C seed ij kl)
      (fun ij => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_self
        f C seed ij)
      (fun ij kl => SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl)

/-- The global zero scheme of the normalized Serre pencil, obtained by
gluing the affine product-chart zero loci over the projective parameter line. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedScheme
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) :
    Scheme :=
  (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroSchemeGlueData
    f C seed).glued

/-- The open chart from a normalized local zero locus into the globally
glued projective-line pencil zero scheme. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subscheme ⟶
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedScheme
        f C seed :=
  (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroSchemeGlueData
    f C seed).ι ij

/-- Each local zero-locus chart embeds openly into the global glued pencil
zero scheme. -/
instance
    SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroGluedι
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed ij) := by
  exact Scheme.GlueData.ι_isOpenImmersion
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroSchemeGlueData
      f C seed) ij

/-- The local zero-locus charts jointly cover the glued projective-line
pencil zero scheme. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι_jointly_surjective
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (x : SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedScheme
      f C seed) :
    ∃ (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
      (y : (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subscheme),
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed ij y = x := by
  obtain ⟨ij, y, hy⟩ := Scheme.GlueData.ι_jointly_surjective
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroSchemeGlueData
      f C seed) x
  exact ⟨ij, y, hy⟩

/-- The pairwise transition identifies the local zero-locus charts in the
globally glued projective-line pencil zero scheme. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι_glue
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
      f C seed ij kl).hom ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed kl ij ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed kl =
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed ij :=
  Scheme.GlueData.glue_condition
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroSchemeGlueData
      f C seed) ij kl

/-- The local closed zero loci have compatible maps to the projective-line
ambient product, so the gluing carries a canonical ambient morphism. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedScheme
      f C seed ⟶ projectiveLineAmbient K f :=
  AllCharacteristics.OverlapComposition.gluedDescTo
    (fun ij => (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subscheme)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
      f C seed ij kl)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed ij kl)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
      f C seed ij kl)
    (fun ij kl => (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
      f C seed ij kl).hom)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_left_eq_rightMap
      f C seed ij kl)
    (fun ij kl mn => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross
      f C seed ij kl mn)
    (fun ij kl mn => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross_fac
      f C seed ij kl mn)
    (fun ij kl mn => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross_right
      f C seed ij kl mn)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_swap_hom
      f C seed ij kl)
    (fun ij => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_self
      f C seed ij)
    (fun ij kl => SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed ij kl)
    (fun ij =>
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    (fun ij kl =>
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_comp_subschemeι_comp_chart
        f C seed ij kl).symm)

/-- On each product chart, the ambient map of the glued zero scheme is the
original local closed-immersion map. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι_comp_toAmbient
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed ij ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed =
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subschemeι ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij :=
  AllCharacteristics.OverlapComposition.ι_gluedDescTo
    (fun ij => (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subscheme)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
      f C seed ij kl)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed ij kl)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
      f C seed ij kl)
    (fun ij kl => (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
      f C seed ij kl).hom)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_left_eq_rightMap
      f C seed ij kl)
    (fun ij kl mn => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross
      f C seed ij kl mn)
    (fun ij kl mn => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross_fac
      f C seed ij kl mn)
    (fun ij kl mn => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroTripleOverlapCross_right
      f C seed ij kl mn)
    (fun ij kl => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_hom_comp_swap_hom
      f C seed ij kl)
    (fun ij => SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap_self
      f C seed ij)
    (fun ij kl => SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed ij kl)
    (fun ij =>
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    (fun ij kl =>
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap_comp_subschemeι_comp_chart
        f C seed ij kl).symm)
    ij

/-- The local zero locus on a product chart maps to the pullback of the
globally glued zero scheme over that chart. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subscheme ⟶
      pullback
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) :=
  pullback.lift
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
      f C seed ij)
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subschemeι
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι_comp_toAmbient
      f C seed ij)

/-- The first projection of the local-to-global pullback comparison is the
glued chart map. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι_comp_fst
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
        f C seed ij ≫
      pullback.fst
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed ij :=
  pullback.lift_fst _ _ _

/-- The second projection of the local-to-global pullback comparison is the
original local closed immersion. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι_comp_snd
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
        f C seed ij ≫
      pullback.snd
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) =
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι :=
  pullback.lift_snd _ _ _

/-- The range of a glued local zero chart lies in the corresponding target
pullback over the ambient product chart. -/
theorem
    SerreExtensionRankTwoAffineCover.range_projectiveLineNormalizedLocalPencilZeroGluedι_subset_targetPullbackFst
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    Set.range (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
      f C seed ij) ⊆
      Set.range (pullback.fst
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)) := by
  rw [IsOpenImmersion.range_pullbackFst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed)]
  rintro x ⟨y, rfl⟩
  change (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed ij y) ∈
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij).opensRange
  rw [← Scheme.Hom.comp_apply,
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι_comp_toAmbient]
  exact ⟨_, rfl⟩

/-- A local zero-locus point whose ambient image lies in a second product
chart comes from the explicit pairwise overlap zero locus. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLineNormalizedLocalPencilZeroOverlap_of_mem
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij kl : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (y : (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subscheme)
    (hy : ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subschemeι ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) y ∈
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl).opensRange) :
    ∃ z : SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlap
      f C seed ij kl,
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl z = y := by
  let a := pullback.fst
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)
  let I := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij
  have hmem : I.subschemeι y ∈ a.opensRange := by
    change I.subschemeι y ∈ (pullback.fst
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl)).opensRange
    rw [Scheme.Hom.opensRange_pullbackFst]
    exact hy
  obtain ⟨z, hz⟩ := (IsOpenImmersion.range_pullbackSnd a I.subschemeι).ge hmem
  refine ⟨(I.comapIso a).inv z, ?_⟩
  change (((I.comapIso a).inv ≫ (I.comapIso a).hom) ≫ pullback.snd a I.subschemeι) z = y
  rw [Iso.inv_hom_id, Category.id_comp]
  exact hz

/-- Each local zero locus is the full pullback of the glued zero scheme over
its ambient product chart. -/
theorem
    SerreExtensionRankTwoAffineCover.range_projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι_eq_univ
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    Set.range (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
      f C seed ij) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨kl, y, hy⟩ :=
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι_jointly_surjective
      f C seed
      (pullback.fst
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) p)
  have hyUi : ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed kl).subschemeι ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f kl) y ∈
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij).opensRange := by
    rw [← SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι_comp_toAmbient]
    change (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed)
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed kl y) ∈
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij).opensRange
    rw [hy]
    rw [← Scheme.Hom.comp_apply, pullback.condition]
    exact Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩
  obtain ⟨w, hw⟩ :=
    SerreExtensionRankTwoAffineCover.exists_projectiveLineNormalizedLocalPencilZeroOverlap_of_mem
      f C seed kl ij y hyUi
  refine ⟨SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapRightMap
    f C seed kl ij w, ?_⟩
  apply (pullback.fst
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)).isEmbedding.injective
  rw [← Scheme.Hom.comp_apply,
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι_comp_fst]
  rw [← hy, ← hw]
  change (((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapSwap
    f C seed kl ij).hom ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
        f C seed ij kl) ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed ij) w =
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroOverlapι
      f C seed kl ij ≫
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed kl) w
  exact congrArg (fun q => q w)
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι_glue
      f C seed kl ij)

/-- The local-to-global comparison into the target pullback is an open
immersion. -/
theorem
    SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
        f C seed ij) := by
  let hrange : Set.range
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed ij) ⊆
      Set.range (pullback.fst
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)) :=
    SerreExtensionRankTwoAffineCover.range_projectiveLineNormalizedLocalPencilZeroGluedι_subset_targetPullbackFst
      f C seed ij
  let l := IsOpenImmersion.lift
    (pullback.fst
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij))
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
      f C seed ij) hrange
  have hl : SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
      f C seed ij = l := by
    apply (cancel_mono (pullback.fst
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij))).mp
    rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι_comp_fst]
    exact (IsOpenImmersion.lift_fac
      (pullback.fst
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij))
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed ij) hrange).symm
  rw [hl]
  change IsOpenImmersion (IsOpenImmersion.lift
    (pullback.fst
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij))
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
      f C seed ij) hrange)
  infer_instance

/-- The local zero locus is isomorphic to the pullback of the glued scheme
over its ambient product chart. -/
theorem
    SerreExtensionRankTwoAffineCover.isIso_projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsIso
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
        f C seed ij) := by
  letI : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
        f C seed ij) :=
    SerreExtensionRankTwoAffineCover.isOpenImmersion_projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
      f C seed ij
  have hopen : (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
      f C seed ij).opensRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    exact SerreExtensionRankTwoAffineCover.range_projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι_eq_univ
      f C seed ij
  exact isIso_of_isOpenImmersion_of_opensRange_eq_top
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
      f C seed ij) hopen

/-- Over every product chart, the target pullback of the glued ambient map is
the local closed zero locus. -/
theorem
    SerreExtensionRankTwoAffineCover.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackSnd
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    [IsIso (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
      f C seed ij)] :
    IsClosedImmersion
      (pullback.snd
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed)
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)) := by
  let E := asIso
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
      f C seed ij)
  have h : pullback.snd
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) =
      E.inv ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed ij).subschemeι := by
    rw [← cancel_epi E.hom]
    simpa [E] using
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι_comp_snd
        f C seed ij)
  rw [h]
  infer_instance

/-- The zero scheme obtained by gluing the normalized local pencil equations
is a closed subscheme of the projective-line ambient product. -/
theorem
    SerreExtensionRankTwoAffineCover.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedToAmbient
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) :
    IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed) := by
  apply IsZariskiLocalAtTarget.of_openCover
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C)
  intro ij
  letI : IsIso
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
        f C seed ij) :=
    SerreExtensionRankTwoAffineCover.isIso_projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
      f C seed ij
  exact SerreExtensionRankTwoAffineCover.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackSnd
    f C seed ij

/-- Each normalized local pencil zero locus is affine.  This exposes the
remaining flatness calculation as a statement about its actual coordinate
algebra over the corresponding standard affine chart of the parameter line. -/
theorem
    SerreExtensionRankTwoAffineCover.isAffine_projectiveLineNormalizedLocalPencilZero
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsAffine
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subscheme := by
  letI : IsAffine ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_affine f C ij
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι := inferInstance
  exact isAffine_of_isAffineHom
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij).subschemeι

/-- A fibrewise regular pair of the two local pencil coordinates makes the
actual normalized local zero scheme flat over its affine parameter chart. -/
theorem
    SerreExtensionRankTwoAffineCover.flat_projectiveLineNormalizedLocalPencilZero_toLineChart_of_two_nonZeroDivisors
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (p q : Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤))
    (hzero :
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal f C seed ij =
        AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
          (Ideal.span {p} ⊔ Ideal.span {q}))
    (hambient :
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.Flat)
    (hp : ∀ L : Ideal Γ((lineProjOpenCover K).X ij.2, ⊤),
      Ideal.Quotient.mk
          (L.map
            (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
              f C ij).appTop.hom) p ∈
        (Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤) ⧸
          L.map
            (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
              f C ij).appTop.hom)⁰)
    (hq : ∀ L : Ideal Γ((lineProjOpenCover K).X ij.2, ⊤),
      Ideal.Quotient.mk
          (L.map
            ((Ideal.Quotient.mk (Ideal.span {p})).comp
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
                f C ij).appTop.hom))
          (Ideal.Quotient.mk (Ideal.span {p}) q) ∈
        ((Γ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij, ⊤) ⧸
          Ideal.span {p}) ⧸
          L.map
            ((Ideal.Quotient.mk (Ideal.span {p})).comp
              (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
                f C ij).appTop.hom))⁰) :
    Flat
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
  let _ : IsAffine ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij) :=
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_affine f C ij
  let _ : IsAffine ((lineProjOpenCover K).X ij.2) := by
    change IsAffine (Spec _)
    infer_instance
  apply AllCharacteristics.flat_subscheme_comp_of_flat_quotient_eq
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij)
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal f C seed ij)
    (Ideal.span {p} ⊔ Ideal.span {q})
  · rw [hzero, AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal]
    simp
  · exact AllCharacteristics.quotient_flat_of_two_nonZeroDivisors_over_ringHom
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom
      hambient p q hp hq

/-- For a flat original family, fibrewise regularity of the two actual
normalized pencil coordinates gives flatness of its local zero scheme over
the parameter-line chart. -/
theorem
    SerreExtensionRankTwoAffineCover.flat_projectiveLineNormalizedLocalPencilZero_toLineChart_of_fibrewiseRegularCoordinates
    [IsSeparated f] [Flat f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hregular : AllCharacteristics.IsFibrewiseRegularPair
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2) :
    Flat
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
  apply SerreExtensionRankTwoAffineCover.flat_projectiveLineNormalizedLocalPencilZero_toLineChart_of_two_nonZeroDivisors
    f C seed ij
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
      f C seed ij).1
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
      f C seed ij).2
  · exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_eq_coordinates
      f C seed ij
  · let _ : Flat
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) :=
      SerreExtensionRankTwoAffineCover.flat_projectiveLineOpenCover_toLineChart f C ij
    let _ : IsAffine ((lineProjOpenCover K).X ij.2) := by
      change IsAffine (Spec _)
      infer_instance
    exact Scheme.Hom.flat_appTop _
  · exact hregular.1
  · exact hregular.2

/-- A flatness calculation on the coordinate algebra of a normalized local
zero locus yields flatness of that local zero locus over its affine parameter
chart. -/
theorem
    SerreExtensionRankTwoAffineCover.flat_projectiveLineNormalizedLocalPencilZero_toLineChart_of_flat_appTop
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hflat :
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.Flat) :
    Flat
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
  letI : IsAffine
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subscheme :=
    SerreExtensionRankTwoAffineCover.isAffine_projectiveLineNormalizedLocalPencilZero
      f C seed ij
  letI : IsAffine ((lineProjOpenCover K).X ij.2) := by
    change IsAffine (Spec _)
    infer_instance
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  exact hflat

/-- Flatness of the global normalized Serre-pencil zero scheme follows from
the affine coordinate-algebra flatness calculations on the local zero loci.
The latter are the concrete regular-sequence calculations still required by
Voisin's construction. -/
theorem
    SerreExtensionRankTwoAffineCover.flat_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_flat_appTop
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hflat : ∀ ij,
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom.Flat) :
    Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  letI : HasAffineProperty @Flat (sourceAffineLocally RingHom.Flat) :=
    HasRingHomProperty.HasAffineProperty @Flat
  letI : IsZariskiLocalAtSource @Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @Flat)
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroSchemeGlueData
      f C seed).openCover).mpr
  change ∀ ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀,
    Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed ij ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)))
  intro ij
  rw [← Category.assoc,
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι_comp_toAmbient,
    Category.assoc,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLine]
  letI : Flat
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) :=
    SerreExtensionRankTwoAffineCover.flat_projectiveLineNormalizedLocalPencilZero_toLineChart_of_flat_appTop
      f C seed ij (hflat ij)
  rw [← Category.assoc]
  exact Flat.comp _ _

/-- If the two named normalized coordinates are fibrewise regular on every
product chart, their glued pencil zero scheme is flat over the projective
parameter line.  This combines the local regular-sequence calculation with
Zariski descent for flatness. -/
theorem
    SerreExtensionRankTwoAffineCover.flat_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_fibrewiseRegularCoordinates
    [IsSeparated f] [Flat f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hregular : ∀ ij, AllCharacteristics.IsFibrewiseRegularPair
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2) :
    Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  apply SerreExtensionRankTwoAffineCover.flat_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_flat_appTop
    f C seed
  intro ij
  letI : Flat
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) :=
    SerreExtensionRankTwoAffineCover.flat_projectiveLineNormalizedLocalPencilZero_toLineChart_of_fibrewiseRegularCoordinates
      f C seed ij (hregular ij)
  letI : IsAffine
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subscheme :=
    SerreExtensionRankTwoAffineCover.isAffine_projectiveLineNormalizedLocalPencilZero
      f C seed ij
  letI : IsAffine ((lineProjOpenCover K).X ij.2) := by
    change IsAffine (Spec _)
    infer_instance
  exact Scheme.Hom.flat_appTop _

/-- If the original surface is proper over the coefficient field, then the
glued zero scheme is proper over the parameter line.  Thus the remaining
finiteness proof for the Serre pencil reduces to its quasi-finiteness. -/
theorem
    SerreExtensionRankTwoAffineCover.isProper_projectiveLineNormalizedLocalPencilZeroGluedToLine
    [IsProper f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) :
    IsProper
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed
  infer_instance

/-- Properness of the glued pencil over the projective line also gives local
finite presentation: the projective line over a field is locally
Noetherian. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyOfFinitePresentation_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_isProper
    [IsNoetherianRing K] [IsProper f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) :
    LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  letI : IsProper
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.isProper_projectiveLineNormalizedLocalPencilZeroGluedToLine
      f C seed
  letI : IsLocallyNoetherian (projectiveLineProj K) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveLineProjToBase K)
  rw [LocallyOfFinitePresentation.iff_locallyOfFiniteType]
  infer_instance

/-- For a proper surface, quasi-finiteness of the glued pencil over the
parameter line already implies its finiteness.  This isolates the
dimension-zero fiber calculation as the remaining part of finiteness. -/
theorem
    SerreExtensionRankTwoAffineCover.isFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_locallyQuasiFinite
    [IsProper f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))] :
    IsFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  letI : IsProper
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.isProper_projectiveLineNormalizedLocalPencilZeroGluedToLine
      f C seed
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- Local quasi-finiteness of the normalized zero locus on every product
chart descends to the glued Serre pencil.  This lets the dimension calculation
for a selected cubic be made on the actual affine zero-locus charts. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hlocal : ∀ ij, LocallyQuasiFinite
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij)) :
    LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  letI : IsZariskiLocalAtSource @LocallyQuasiFinite :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @LocallyQuasiFinite)
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroSchemeGlueData
      f C seed).openCover).mpr
  change ∀ ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀,
    LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed ij ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)))
  intro ij
  rw [← Category.assoc,
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι_comp_toAmbient,
    Category.assoc,
    SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLine]
  letI : LocallyQuasiFinite
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) :=
    hlocal ij
  rw [← Category.assoc]
  infer_instance

/-- When the quotient calculation is available on every affine product
chart, the normalized Serre-pencil zero scheme is locally quasi-finite over
the projective parameter line. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_artinian_coordinate_quotients
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hartinian : ∀ ij,
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateQuotientArtinianFibers
        f C seed ij) :
    LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  apply
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local
      f C seed
  intro ij
  letI : LocallyOfFiniteType (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk
        (Ideal.span
          {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
            f C seed ij).1} ⊔
          Ideal.span
            {(SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
              f C seed ij).2})).comp
        (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
          f C ij).appTop.hom))) := (hartinian ij).locallyOfFiniteType
  exact
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZero_toLineChart_of_artinian_coordinate_quotients
      f C seed ij (hartinian ij).fiber_artinian

/-- If the surface family is locally of finite type, the Artinian
two-coordinate quotient calculation on every product chart makes the glued
normalized Serre pencil locally quasi-finite.  No separate chartwise
finite-type datum is required. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_artinian_coordinate_fibers
    [IsSeparated f] [LocallyOfFiniteType f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hartinian : ∀ ij,
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers
        f C seed ij) :
    LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  apply
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local
      f C seed
  intro ij
  exact
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZero_toLineChart_of_artinian_coordinate_fibers
      f C seed ij (hartinian ij)

/-- Successive cotangent-parameter calculations on all normalized pencil
charts make the glued zero scheme locally quasi-finite over the parameter
line.  This is the global dimension-zero conclusion supplied by a
chartwise Jacobian/transversality proof on a smooth relative surface. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_successiveRegularParameters_of_smoothOfRelativeDimension_two
    [IsSeparated f] [LocallyOfFiniteType f] [SmoothOfRelativeDimension 2 f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hparameters : ∀ ij,
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateSuccessiveRegularParameters
        f C seed ij) :
    LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  apply
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_artinian_coordinate_fibers
      f C seed
  intro ij
  exact
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_local_successiveRegularParameters_of_smoothOfRelativeDimension_two_ofLocallyOfFiniteType
      f C seed ij (hparameters ij)

/-- Direct rank-two cotangent calculations on all normalized pencil charts
make the actual glued zero scheme locally quasi-finite over the parameter
line.  This is the global zero-dimensionality consequence of the Jacobian
rank condition on a smooth relative surface. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_cotangentIndependentParameters_of_smoothOfRelativeDimension_two
    [IsSeparated f] [LocallyOfFiniteType f] [SmoothOfRelativeDimension 2 f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hparameters : ∀ ij,
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateCotangentIndependentParameters
        f C seed ij) :
    LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  apply
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_artinian_coordinate_fibers
      f C seed
  intro ij
  exact
    SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_local_cotangentIndependentParameters_of_smoothOfRelativeDimension_two_ofLocallyOfFiniteType
      f C seed ij (hparameters ij)

/- A chartwise Jacobian span certificate supplies the smooth-relative-surface
   instance needed by the preceding theorem.  This specialization records the
   precise cubic-hypersurface interface: the remaining input is the direct
   cotangent independence of the two normalized pencil coordinates. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_cotangentIndependentParameters_of_hypersurfaceChartPDerivSpan
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hspan : ∀ j : Fin 4,
      Ideal.span (Set.range (chartPDeriv p hp j)) = ⊤)
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    {e : SerreExtensionData (hypersurface p hp) M}
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hparameters : ∀ ij,
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateCotangentIndependentParameters
        (hypersurfaceToBase p hp) C seed ij) :
    LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        (hypersurfaceToBase p hp) C seed ≫
        pullback.snd (hypersurfaceToBase p hp) (projectiveLineProjToBase K)) := by
  letI : SmoothOfRelativeDimension 2 (hypersurfaceToBase p hp) :=
    smoothOfRelativeDimension_two_hypersurface_of_chart_pderiv_span p hp hspan
  exact
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_cotangentIndependentParameters_of_smoothOfRelativeDimension_two
      (hypersurfaceToBase p hp) C seed hparameters

/-- Artinianness of the actual zero-locus fibres on one affine product chart.
Packaging this dependent chartwise statement keeps later local-to-global
arguments from having to elaborate the full fibre expression repeatedly. -/
structure SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilArtinianFibers
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) : Prop where
  fiber_artinian : ∀ x : (lineProjOpenCover K).X ij.2,
    IsArtinianScheme
      (((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).fiber x)

/-- On a single affine product chart, Artinianness of the actual parameter
fibres implies local quasi-finiteness of the normalized zero locus.  Together
with the preceding descent theorem, this is the chartwise form of Voisin's
zero-dimensionality conclusion. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZero_toLineChart_of_artinian_fibers
    [IsNoetherianRing K] [IsProper f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hartinian : ∀ x : (lineProjOpenCover K).X ij.2,
      IsArtinianScheme
        (((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed ij).subschemeι ≫
          SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).fiber x)) :
    LocallyQuasiFinite
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) := by
  let g := (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
    f C seed ij).subschemeι ≫
      SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij
  let G := SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
    f C seed ≫ pullback.snd f (projectiveLineProjToBase K)
  letI : LocallyOfFinitePresentation G :=
    SerreExtensionRankTwoAffineCover.locallyOfFinitePresentation_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_isProper
      f C seed
  letI : LocallyOfFiniteType G := inferInstance
  have hgcomp : g ≫ (lineProjOpenCover K).f ij.2 =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
        f C seed ij ≫ G := by
    dsimp only [g, G]
    calc
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij).subschemeι ≫
        SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij) ≫
          (lineProjOpenCover K).f ij.2 =
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed ij).subschemeι ≫
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij ≫
            (lineProjOpenCover K).f ij.2) := by
          simp only [Category.assoc]
      _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed ij).subschemeι ≫
          ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij ≫
            pullback.snd f (projectiveLineProjToBase K)) := by
          rw [← SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLine]
      _ = ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed ij).subschemeι ≫
          (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) ≫
            pullback.snd f (projectiveLineProjToBase K) := by
          simp only [Category.assoc]
      _ = (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
          f C seed ij ≫
          SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
            f C seed) ≫ pullback.snd f (projectiveLineProjToBase K) := by
          rw [SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι_comp_toAmbient]
      _ = SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedι
          f C seed ij ≫ G := by
          rfl
  letI : LocallyOfFiniteType (g ≫ (lineProjOpenCover K).f ij.2) := by
    rw [hgcomp]
    infer_instance
  letI : LocallyOfFiniteType g :=
    locallyOfFiniteType_of_comp g ((lineProjOpenCover K).f ij.2)
  apply LocallyQuasiFinite.of_fiberToSpecResidueField
  intro x
  letI : IsArtinianScheme (g.fiber x) := hartinian x
  letI : LocallyOfFiniteType (g.fiberToSpecResidueField x) := by
    change LocallyOfFiniteType (pullback.snd _ _)
    infer_instance
  letI : LocallyQuasiFinite (g.fiberToSpecResidueField x) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fun _ ↦ Set.toFinite _)
  letI : IsFinite (g.fiberToSpecResidueField x) :=
    IsFinite.of_locallyQuasiFinite _
  infer_instance

/-- Chartwise Artinianness of the normalized zero loci makes the full glued
Serre pencil locally quasi-finite over the projective parameter line. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_artinian_fibers
    [IsNoetherianRing K] [IsSeparated f] [IsProper f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hartinian : ∀ ij,
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilArtinianFibers
        f C seed ij) :
    LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  apply
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local
      f C seed
  intro ij
  apply
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZero_toLineChart_of_artinian_fibers
      f C seed ij
  exact (hartinian ij).fiber_artinian

/-- To prove the glued pencil locally quasi-finite, it suffices to prove that
each of its actual residue-field fibers is finite.  This is the precise
scheme-theoretic form of the zero-dimensional-fiber assertion in Voisin's
generic-section argument. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_finite_fibers
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hfinite : ∀ x : projectiveLineProj K,
      IsFinite
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiberToSpecResidueField x)) :
    LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  apply LocallyQuasiFinite.of_fiberToSpecResidueField
  intro x
  letI : IsFinite
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiberToSpecResidueField x) :=
    hfinite x
  infer_instance

/-- On each fibre over the parameter line, Voisin's zero-dimensionality conclusion may be
expressed by Artinianness.  Properness supplies finite type, so an Artinian fibre is finite over
its residue field and hence the glued pencil is locally quasi-finite. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_artinian_fibers
    [IsNoetherianRing K] [IsProper f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hartinian : ∀ x : projectiveLineProj K,
      IsArtinianScheme
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiber x)) :
    LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  letI : LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.locallyOfFinitePresentation_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_isProper
      f C seed
  letI : LocallyOfFiniteType
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    inferInstance
  apply LocallyQuasiFinite.of_fiberToSpecResidueField
  intro x
  letI : IsArtinianScheme
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiber x) :=
    hartinian x
  letI : LocallyOfFiniteType
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiberToSpecResidueField x) := by
    change LocallyOfFiniteType (pullback.snd _ _)
    infer_instance
  letI : LocallyQuasiFinite
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiberToSpecResidueField x) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fun _ ↦ Set.toFinite _)
  letI : IsFinite
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiberToSpecResidueField x) :=
    IsFinite.of_locallyQuasiFinite _
  infer_instance

/-- A dimension-zero fibre in the proper rank-two pencil is Artinian.  This converts the usual
geometric formulation of Voisin's generic-section lemma into the fibre hypothesis used above. -/
theorem
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_topologicalKrullDim_le_zero_fibers
    [IsNoetherianRing K] [IsProper f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hzero : ∀ x : projectiveLineProj K,
      topologicalKrullDim
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiber x) ≤ 0) :
    LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) := by
  letI : IsProper
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.isProper_projectiveLineNormalizedLocalPencilZeroGluedToLine
      f C seed
  letI : LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.locallyOfFinitePresentation_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_isProper
      f C seed
  letI : LocallyOfFiniteType
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    inferInstance
  apply
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_artinian_fibers
      f C seed
  intro x
  letI : LocallyOfFiniteType
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiberToSpecResidueField x) := by
    change LocallyOfFiniteType (pullback.snd _ _)
    infer_instance
  letI : QuasiCompact
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiberToSpecResidueField x) := by
    change QuasiCompact (pullback.snd _ _)
    infer_instance
  letI : IsLocallyNoetherian (Spec (.of ((projectiveLineProj K).residueField x))) := by
    infer_instance
  letI : IsLocallyNoetherian
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiber x) :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiberToSpecResidueField x)
  letI : IsLocallyArtinian
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiber x) :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero (hzero x)
  letI : CompactSpace
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiber x) :=
    QuasiCompact.compactSpace_of_compactSpace
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiberToSpecResidueField x)
  exact ⟨⟩

/-- Pulling the ideal of the glued closed pencil zero scheme back to a product
chart recovers the normalized local zero ideal on that chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient_ker_comap
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed).ker.comap
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)).hom,
    pullbackSymmetry_hom_comp_fst]
  letI : IsIso
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
        f C seed ij) :=
    SerreExtensionRankTwoAffineCover.isIso_projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
      f C seed ij
  let E := asIso
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι
      f C seed ij)
  have h : pullback.snd
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed)
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) =
      E.inv ≫
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
          f C seed ij).subschemeι := by
    rw [← cancel_epi E.hom]
    simpa [E] using
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedTargetPullbackι_comp_snd
        f C seed ij)
  rw [h, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_subschemeι]

/-- Once its finite-flat and constant-rank properties have been established,
the glued pencil zero scheme gives the corresponding ideal-defined finite
subscheme of the projective-line family. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    (n : ℕ)
    (hn : ∀ s : projectiveLineProj K,
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank s = n) :
    AllCharacteristics.FiniteSubschemeDatum
      (pullback.snd f (projectiveLineProjToBase K)) n := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed
  exact AllCharacteristics.finiteSubschemeDatumOfClosedImmersion
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed)
    (pullback.snd f (projectiveLineProjToBase K)) n hn

/-- Under the finite-flat hypotheses, the finite-subscheme datum obtained
from the glued zero scheme has the prescribed normalized ideal on every
product chart. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum_localIdeal_eq
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    (n : ℕ)
    (hn : ∀ s : projectiveLineProj K,
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank s = n)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum
      f C seed n hn).val.comap
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed
  change (AllCharacteristics.finiteSubschemeDatumOfClosedImmersion
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed)
    (pullback.snd f (projectiveLineProjToBase K)) n hn).val.comap
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) = _
  rw [AllCharacteristics.finiteSubschemeDatumOfClosedImmersion_ideal]
  exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient_ker_comap
    f C seed ij

/-- The source of the glued pencil zero scheme is canonically the closed
subscheme underlying its associated finite-subscheme datum. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatumIso
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    (n : ℕ)
    (hn : ∀ s : projectiveLineProj K,
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank s = n) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedScheme
      f C seed ≅
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum
        f C seed n hn).val.subscheme := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed
  exact AllCharacteristics.finiteSubschemeDatumOfClosedImmersionIso
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed)
    (pullback.snd f (projectiveLineProjToBase K)) n hn

/-- The finite-subscheme identification preserves the ambient projective-line
family immersion. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatumIso_hom_ι
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    (n : ℕ)
    (hn : ∀ s : projectiveLineProj K,
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank s = n) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatumIso
      f C seed n hn).hom ≫
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum
        f C seed n hn).val.subschemeι =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed
  exact AllCharacteristics.finiteSubschemeDatumOfClosedImmersionIso_hom_ι
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed)
    (pullback.snd f (projectiveLineProjToBase K)) n hn

/-- View the normalized zero ideal on one affine product chart as an ideal
sheaf on the whole parameter space.  Its restriction back to that chart is
proved below; this is the ambient closed-subscheme model from which the
global finite-flat pencil will be assembled. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdealExtension
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (projectiveLineAmbient K f).IdealSheafData :=
  AllCharacteristics.openKernelExtension
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)

/-- Restriction of the ambient kernel extension of a normalized local
zero-locus recovers exactly the local coordinate ideal. -/
theorem
    SerreExtensionRankTwoAffineCover.comap_projectiveLineNormalizedLocalPencilZeroIdealExtension
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdealExtension
      f C seed ij).comap
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij := by
  letI : (projectiveLineAmbient K f).IsSeparated :=
    projectiveLineAmbient_isSeparated f
  exact AllCharacteristics.idealSheafData_comap_ker_subscheme_comp_open_of_isAffine
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed ij)
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij)

/-- The local ideal on the true chart is computed from the slope--lift
equation. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_of_eq_true
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 = true) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal f C seed ij =
      SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilZeroIdealOf f C seed ij
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij) (𝟙 _) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
  rw [SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients_of_eq_true
    f C ij hij]

/-- The local ideal on the false chart is computed from the
canonical--slope equation. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_of_eq_false
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (hij : ij.2 = false) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal f C seed ij =
      SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilZeroIdealOf f C seed ij
        (𝟙 _) (SerreExtensionRankTwoAffineCover.projectiveLineLocalCoordinateCoefficient f C ij) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
  rw [SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients_of_eq_false
    f C ij hij]

/-- The canonical generator of the pencil, transported to the actual
pullback of the global Serre bundle on a parameter chart. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSectionOnGlobalBundle
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij ≫
        projectiveLineAmbientToScheme K f)).obj e.E).sections :=
  SheafOfModules.sectionsMap
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModuleIso f C ij).hom
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSection f C ij)

/-- The lifted generator of the pencil, transported to the actual pullback
of the global Serre bundle on a parameter chart. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSectionOnGlobalBundle
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij ≫
        projectiveLineAmbientToScheme K f)).obj e.E).sections :=
  SheafOfModules.sectionsMap
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModuleIso f C ij).hom
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSection f C seed ij)

/-- Transport from a local trivialization to the global pulled-back bundle
commutes with forming every scalar linear combination of the two pencil
generators. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineLocalModuleIso_hom_pencilSectionOf
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (a b : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf) :
    SheafOfModules.sectionsMap
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalModuleIso f C ij).hom
      (SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf f C seed ij a b) =
    BundleSectionZeroLocus.addSections
      (BundleSectionZeroLocus.scaleSection a
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSectionOnGlobalBundle
          f C ij))
      (BundleSectionZeroLocus.scaleSection b
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSectionOnGlobalBundle
          f C seed ij)) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSectionOf
  rw [BundleSectionZeroLocus.sectionsMap_addSections,
    BundleSectionZeroLocus.sectionsMap_scaleSection,
    BundleSectionZeroLocus.sectionsMap_scaleSection]
  rfl

/-- The normalized local section transported to the actual pullback of the
global Serre bundle. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSectionOnGlobalBundle
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij ≫
        projectiveLineAmbientToScheme K f)).obj e.E).sections :=
  SheafOfModules.sectionsMap
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModuleIso f C ij).hom
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection f C seed ij)

/-- In the actual pulled-back Serre bundle, the normalized section is the
normalized scalar linear combination of the transported canonical and lifted
generators. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSectionOnGlobalBundle_eq
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSectionOnGlobalBundle
      f C seed ij =
    BundleSectionZeroLocus.addSections
      (BundleSectionZeroLocus.scaleSection
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C ij).1
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalCanonicalSectionOnGlobalBundle
          f C ij))
      (BundleSectionZeroLocus.scaleSection
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalNormalizedCoefficients f C ij).2
        (SerreExtensionRankTwoAffineCover.projectiveLineLocalLiftSectionOnGlobalBundle
          f C seed ij)) := by
  unfold SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSectionOnGlobalBundle
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection
  exact SerreExtensionRankTwoAffineCover.projectiveLineLocalModuleIso_hom_pencilSectionOf
    f C seed ij _ _

/-- The chart zero ideal computed after transporting the normalized local
section to the actual pullback of the global bundle. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdealOnGlobalBundle
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    AlgebraicGeometry.Scheme.IdealSheafData
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalGlobalFreeIso f C ij)
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSectionOnGlobalBundle
      f C seed ij)

/-- Transporting the local module to the pullback of the global bundle leaves
the normalized coordinate zero ideal unchanged. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_eq_onGlobalBundle
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal f C seed ij =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdealOnGlobalBundle
        f C seed ij := by
  exact BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_postcompose_eq
    (ULift.{u} (Fin 2))
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalFreeIso f C ij)
    (SerreExtensionRankTwoAffineCover.projectiveLineLocalModuleIso f C ij)
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilSection f C seed ij)

end

section

variable {K : Type u} [Field K] {X : Scheme.{u}}
  {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
  (f : X ⟶ Spec (.of K))

/-- The rank of a finite flat finitely presented glued pencil is determined
by its zero endpoint, because the parameter projective line is
preconnected. -/
theorem
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGlued_finrank_eq_zeroEndpoint
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    (s : projectiveLineProj K) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
      f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank s =
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank
        (projectiveLineEndpoint K false (IsLocalRing.closedPoint K)) :=
  (Scheme.Hom.isLocallyConstant_finrank _).apply_eq_of_preconnectedSpace _ _

/-- Once the glued pencil is finite flat and finitely presented, its rank
does not need to be supplied separately: it is the rank of the zero fiber. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatumOfFiniteFlat
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))] :
    AllCharacteristics.FiniteSubschemeDatum
      (pullback.snd f (projectiveLineProjToBase K))
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank
        (projectiveLineEndpoint K false (IsLocalRing.closedPoint K))) :=
  SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum
    f C seed _
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGlued_finrank_eq_zeroEndpoint
      f C seed)

/-- On a proper surface, a flat glued pencil with locally quasi-finite fibers
is already a finite flat finitely presented family.  Its finite-subscheme
datum therefore needs only those two remaining geometric properties. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatumOfProperFlatLocallyQuasiFinite
    [IsProper f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))] :
    AllCharacteristics.FiniteSubschemeDatum
      (pullback.snd f (projectiveLineProjToBase K))
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank
        (projectiveLineEndpoint K false (IsLocalRing.closedPoint K))) := by
  letI : IsFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.isFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_locallyQuasiFinite
      f C seed
  letI : LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.locallyOfFinitePresentation_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_isProper
      f C seed
  exact
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatumOfFiniteFlat
      f C seed

/-- The finite-flat global form of the normalized rank-two pencil.  Its first
field is a finite subscheme of the actual ambient product; the local equation
field states that its restriction to every affine product chart is the
zero-locus of the normalized Serre section constructed above.  The endpoint
isomorphisms are kept over the original scheme, which is exactly the data
needed by the degree-ten residual argument. -/
structure SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
    [IsSeparated f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (n : ℕ)
    (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n) where
  datum : AllCharacteristics.FiniteSubschemeDatum
    (pullback.snd f (projectiveLineProjToBase K)) n
  localIdeal_eq : ∀ ij,
    datum.val.comap
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
        f C seed ij
  zeroIso :
    (AllCharacteristics.rationalCycleFamily_of_finiteSubschemeDatum f n datum).fiber false ≅
      zeroDatum.val.subscheme
  zero_over : zeroIso.hom ≫ zeroDatum.val.subschemeι =
    (AllCharacteristics.rationalCycleFamily_of_finiteSubschemeDatum f n datum).fiberToScheme false
  infinityIso :
    (AllCharacteristics.rationalCycleFamily_of_finiteSubschemeDatum f n datum).fiber true ≅
      infinityDatum.val.subscheme
  infinity_over : infinityIso.hom ≫ infinityDatum.val.subschemeι =
    (AllCharacteristics.rationalCycleFamily_of_finiteSubschemeDatum f n datum).fiberToScheme true

/-- Once finiteness, flatness, finite presentation, and constant rank have
been proved for the glued zero scheme, it supplies a projective-line pencil
with its literal ideal-theoretic endpoint data.  The remaining geometric
endpoint work is precisely to identify these two data with the intended
zero and infinity subschemes. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedCanonicalPencilData
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    (n : ℕ)
    (hn : ∀ s : projectiveLineProj K,
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank s = n) :
    SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed n
      (AllCharacteristics.finiteSubschemeDatumAtLineEndpoint f n
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum
          f C seed n hn) false)
      (AllCharacteristics.finiteSubschemeDatumAtLineEndpoint f n
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum
          f C seed n hn) true) where
  datum :=
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum
      f C seed n hn
  localIdeal_eq :=
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum_localIdeal_eq
      f C seed n hn
  zeroIso := AllCharacteristics.finiteSubschemeDatumAtLineEndpointFiberIso f n
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum
      f C seed n hn) false
  zero_over := AllCharacteristics.finiteSubschemeDatumAtLineEndpointFiberIso_hom_subschemeι f n
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum
      f C seed n hn) false
  infinityIso := AllCharacteristics.finiteSubschemeDatumAtLineEndpointFiberIso f n
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum
      f C seed n hn) true
  infinity_over := AllCharacteristics.finiteSubschemeDatumAtLineEndpointFiberIso_hom_subschemeι f n
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatum
      f C seed n hn) true

/-- The finite-flat glued pencil gives a projective-line pencil without an
extra rank hypothesis; its two endpoints are its literal base-change data. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedCanonicalPencilDataOfFiniteFlat
    [IsSeparated f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [IsFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))] :
    SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank
        (projectiveLineEndpoint K false (IsLocalRing.closedPoint K)))
      (AllCharacteristics.finiteSubschemeDatumAtLineEndpoint f
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank
          (projectiveLineEndpoint K false (IsLocalRing.closedPoint K)))
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatumOfFiniteFlat
          f C seed) false)
      (AllCharacteristics.finiteSubschemeDatumAtLineEndpoint f
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank
          (projectiveLineEndpoint K false (IsLocalRing.closedPoint K)))
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatumOfFiniteFlat
          f C seed) true) :=
  SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedCanonicalPencilData
    f C seed _
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGlued_finrank_eq_zeroEndpoint
      f C seed)

/-- For the proper cubic-surface setting, flatness and locally quasi-finite
fibers of the glued zero scheme already produce the canonical finite-flat
projective-line pencil. -/
noncomputable def
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedCanonicalPencilDataOfProperFlatLocallyQuasiFinite
    [IsProper f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    [LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))] :
    SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed
      ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank
        (projectiveLineEndpoint K false (IsLocalRing.closedPoint K)))
      (AllCharacteristics.finiteSubschemeDatumAtLineEndpoint f
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank
          (projectiveLineEndpoint K false (IsLocalRing.closedPoint K)))
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatumOfProperFlatLocallyQuasiFinite
          f C seed) false)
      (AllCharacteristics.finiteSubschemeDatumAtLineEndpoint f
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).finrank
          (projectiveLineEndpoint K false (IsLocalRing.closedPoint K)))
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedFiniteSubschemeDatumOfProperFlatLocallyQuasiFinite
          f C seed) true) := by
  letI : IsFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.isFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_locallyQuasiFinite
      f C seed
  letI : LocallyOfFinitePresentation
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.locallyOfFinitePresentation_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_isProper
      f C seed
  exact
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedCanonicalPencilDataOfFiniteFlat
      f C seed

/-- A proper flat Serre-pencil zero scheme whose parameter fibres are
Artinian already gives a finite-flat projective-line pencil.  This is the
global geometric interface for a future proof that the zero locus of the
chosen pencil is flat with zero-dimensional fibres; it does not require a
separate coordinate regular-sequence presentation. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_flatZeroGlued_artinian_fibers
    [IsNoetherianRing K] [IsProper f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    (hartinian : ∀ x : projectiveLineProj K,
      IsArtinianScheme
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiber x)) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed n
        zeroDatum infinityDatum) := by
  letI : LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_artinian_fibers
      f C seed hartinian
  exact ⟨⟨_, _, _,
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedCanonicalPencilDataOfProperFlatLocallyQuasiFinite
      f C seed⟩⟩

/-- In the proper cubic-surface setting, fibrewise regularity of the actual
normalized coordinates and locally quasi-finite fibers construct a
finite-flat projective-line pencil.  Thus no independent global-flatness
datum is needed after the chartwise geometric regularity argument. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_locallyQuasiFinite
    [IsProper f] [Flat f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    (hregular : ∀ ij, AllCharacteristics.IsFibrewiseRegularPair
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed n
        zeroDatum infinityDatum) := by
  letI : Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.flat_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_fibrewiseRegularCoordinates
      f C seed hregular
  exact ⟨⟨_, _, _,
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedCanonicalPencilDataOfProperFlatLocallyQuasiFinite
      f C seed⟩⟩

/-- For a proper smooth relative surface, fibrewise regularity of the
normalized pencil coordinates already constructs the finite-flat pencil. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_of_smoothOfRelativeDimension_two
    [IsProper f] [SmoothOfRelativeDimension 2 f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hregular : ∀ ij, AllCharacteristics.IsFibrewiseRegularPair
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed n
        zeroDatum infinityDatum) := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  letI : Flat f := inferInstance
  letI : LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_artinian_coordinate_fibers
      f C seed (fun ij =>
        SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateArtinianFibers.of_base_fibrewiseRegularCoordinates_of_smoothOfRelativeDimension_two_ofLocallyOfFiniteType
          f C seed ij (hregular ij))
  exact
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_locallyQuasiFinite
      f C seed hregular

/-- For an actual cubic hypersurface, the chartwise Jacobian span
certificate supplies the relative-surface instance consumed by the generic
projective-line pencil theorem.  This leaves only the fibrewise regularity of
the two normalized pencil coordinates as geometric input. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_of_hypersurfaceChartPDerivSpan
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hspan : ∀ j : Fin 4,
      Ideal.span (Set.range (chartPDeriv p hp j)) = ⊤)
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    {e : SerreExtensionData (hypersurface p hp) M}
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hregular : ∀ ij, AllCharacteristics.IsFibrewiseRegularPair
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
        (hypersurfaceToBase p hp) C ij).appTop.hom
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        (hypersurfaceToBase p hp) C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        (hypersurfaceToBase p hp) C seed ij).2) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum
        (hypersurfaceToBase p hp) n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
        (hypersurfaceToBase p hp) C seed n zeroDatum infinityDatum) := by
  letI : SmoothOfRelativeDimension 2 (hypersurfaceToBase p hp) :=
    smoothOfRelativeDimension_two_hypersurface_of_chart_pderiv_span p hp hspan
  exact
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_of_smoothOfRelativeDimension_two
      (hypersurfaceToBase p hp) C seed hregular

theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_flatZeroGlued_local_successiveRegularParameters_of_smoothOfRelativeDimension_two
    [IsProper f] [SmoothOfRelativeDimension 2 f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    (hparameters : ∀ ij,
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateSuccessiveRegularParameters
        f C seed ij) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed n
        zeroDatum infinityDatum) := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  letI : LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_successiveRegularParameters_of_smoothOfRelativeDimension_two
      f C seed hparameters
  exact ⟨⟨_, _, _,
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedCanonicalPencilDataOfProperFlatLocallyQuasiFinite
      f C seed⟩⟩


/-- A proper smooth relative surface with a flat normalized pencil zero
scheme yields the finite-flat projective-line pencil once the normalized
coordinates have rank two in every residue-field cotangent space at their
common zeros.  The cotangent condition supplies quasi-finiteness; flatness
remains a separate geometric assertion about the global zero family. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_flatZeroGlued_local_cotangentIndependentParameters_of_smoothOfRelativeDimension_two
    [IsProper f] [SmoothOfRelativeDimension 2 f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    [Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K))]
    (hparameters : ∀ ij,
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateCotangentIndependentParameters
        f C seed ij) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed n
        zeroDatum infinityDatum) := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  letI : LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_local_cotangentIndependentParameters_of_smoothOfRelativeDimension_two
      f C seed hparameters
  exact ⟨⟨_, _, _,
    SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedCanonicalPencilDataOfProperFlatLocallyQuasiFinite
      f C seed⟩⟩

/-- The two local geometric outputs of Voisin's generic-section argument
construct the finite-flat Serre pencil directly.  Fibrewise regularity of
the normalized coordinate pair gives flatness over the parameter line, while
cotangent-space independence at its common zeros gives the required
zero-dimensional fibers. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_local_cotangentIndependentParameters_of_smoothOfRelativeDimension_two
    [IsProper f] [SmoothOfRelativeDimension 2 f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hregular : ∀ ij, AllCharacteristics.IsFibrewiseRegularPair
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2)
    (hparameters : ∀ ij,
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateCotangentIndependentParameters
        f C seed ij) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed n
        zeroDatum infinityDatum) := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  letI : Flat f := inferInstance
  letI : Flat
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.flat_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_fibrewiseRegularCoordinates
      f C seed hregular
  exact
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_flatZeroGlued_local_cotangentIndependentParameters_of_smoothOfRelativeDimension_two
      f C seed hparameters

/- A single certificate for the local geometric conclusion used by Voisin's
   moving-pencil argument.  On a smooth relative surface, fibrewise
   regularity already supplies the Artinian-fibre calculation, so no separate
   cotangent-independence hypothesis is required. -/
structure SerreExtensionRankTwoAffineCover.ProjectiveLineVoisinLocalGeometry
    [IsSeparated f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) : Prop where
  fibrewiseRegular : ∀ ij,
    AllCharacteristics.IsFibrewiseRegularPair
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
        f C ij).appTop.hom
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2

/-- Fibrewise regularity in `ProjectiveLineVoisinLocalGeometry` is exactly
the chartwise input consumed by the proper smooth projective-line pencil
constructor. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_voisinLocalGeometry_of_smoothOfRelativeDimension_two
    [IsProper f] [SmoothOfRelativeDimension 2 f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hgeometry : SerreExtensionRankTwoAffineCover.ProjectiveLineVoisinLocalGeometry
      f C seed) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed n
        zeroDatum infinityDatum) := by
  exact
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_of_smoothOfRelativeDimension_two
      f C seed hgeometry.fibrewiseRegular

/-- For an actual cubic hypersurface, the chartwise Jacobian span and the
two local outputs of the generic-section argument feed the complete
 projective-line pencil construction in one theorem. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_local_cotangentIndependentParameters_of_hypersurfaceChartPDerivSpan
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hspan : ∀ j : Fin 4,
      Ideal.span (Set.range (chartPDeriv p hp j)) = ⊤)
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    {e : SerreExtensionData (hypersurface p hp) M}
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hregular : ∀ ij, AllCharacteristics.IsFibrewiseRegularPair
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart
        (hypersurfaceToBase p hp) C ij).appTop.hom
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        (hypersurfaceToBase p hp) C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        (hypersurfaceToBase p hp) C seed ij).2)
    (hparameters : ∀ ij,
      SerreExtensionRankTwoAffineCover.ProjectiveLineNormalizedLocalPencilCoordinateCotangentIndependentParameters
        (hypersurfaceToBase p hp) C seed ij) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum
        (hypersurfaceToBase p hp) n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
        (hypersurfaceToBase p hp) C seed n zeroDatum infinityDatum) := by
  letI : SmoothOfRelativeDimension 2 (hypersurfaceToBase p hp) :=
    smoothOfRelativeDimension_two_hypersurface_of_chart_pderiv_span p hp hspan
  exact
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_local_cotangentIndependentParameters_of_smoothOfRelativeDimension_two
      (hypersurfaceToBase p hp) C seed hregular hparameters

/-- The proper rank-two construction gives a finite-flat projective-line
pencil once the normalized coordinates are fibrewise regular and each
residue-field fiber of the glued zero scheme is finite.  These are the two
concrete geometric conclusions supplied by Voisin's generic-section
argument. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_finite_fibers
    [IsProper f] [Flat f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hregular : ∀ ij, AllCharacteristics.IsFibrewiseRegularPair
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2)
    (hfinite : ∀ x : projectiveLineProj K,
      IsFinite
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiberToSpecResidueField x)) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed n
        zeroDatum infinityDatum) := by
  letI : LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_finite_fibers
      f C seed hfinite
  exact
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_locallyQuasiFinite
      f C seed hregular

/-- Voisin's zero-dimensionality conclusion can be supplied directly as Artinianness of every
parameter fibre.  Together with fibrewise regular local coordinates, it constructs the
finite-flat projective-line pencil without a separate finiteness axiom. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_artinian_fibers
    [IsNoetherianRing K] [IsProper f] [Flat f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hregular : ∀ ij, AllCharacteristics.IsFibrewiseRegularPair
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2)
    (hartinian : ∀ x : projectiveLineProj K,
      IsArtinianScheme
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiber x)) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed n
        zeroDatum infinityDatum) := by
  letI : LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_artinian_fibers
      f C seed hartinian
  exact
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_locallyQuasiFinite
      f C seed hregular

/-- In the form used in the geometric argument, it is enough that every parameter fibre of the
section zero scheme has topological Krull dimension zero. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_topologicalKrullDim_le_zero_fibers
    [IsNoetherianRing K] [IsProper f] [Flat f] (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hregular : ∀ ij, AllCharacteristics.IsFibrewiseRegularPair
      (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toLineChart f C ij).appTop.hom
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).1
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
        f C seed ij).2)
    (hzero : ∀ x : projectiveLineProj K,
      topologicalKrullDim
        ((SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
          f C seed ≫ pullback.snd f (projectiveLineProjToBase K)).fiber x) ≤ 0) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed n
        zeroDatum infinityDatum) := by
  letI : LocallyQuasiFinite
      (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroGluedToAmbient
        f C seed ≫ pullback.snd f (projectiveLineProjToBase K)) :=
    SerreExtensionRankTwoAffineCover.locallyQuasiFinite_projectiveLineNormalizedLocalPencilZeroGluedToLine_of_topologicalKrullDim_le_zero_fibers
      f C seed hzero
  exact
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_locallyQuasiFinite
      f C seed hregular

/- If the first normalized coordinate is a unit on every product chart, the
   two geometric certificates required by the proper pencil constructor are
   discharged simultaneously.  This is a convenient sufficient unit-chart
   test.  Voisin's source instead obtains the relevant regularity from a
   generic-section argument, so this theorem is not intended to express that
   remaining geometric input. -/
theorem
    SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_firstNormalizedCoordinate_isUnit
    [IsProper f] [SmoothOfRelativeDimension 2 f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (hunit : ∀ ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀,
      IsUnit
        (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates
          f C seed ij).1) :
    Nonempty (Σ (n : ℕ)
      (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n),
      SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData f C seed n
        zeroDatum infinityDatum) := by
  refine SerreExtensionRankTwoAffineCover.exists_projectiveLinePencilData_of_proper_fibrewiseRegularCoordinates_local_cotangentIndependentParameters_of_smoothOfRelativeDimension_two
    f C seed ?_ ?_
  · intro ij
    exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates_fibrewiseRegular_of_first_isUnit
      f C seed ij (hunit ij)
  · intro ij
    exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilCoordinates_cotangentIndependentParameters_of_first_isUnit
      f C seed ij (hunit ij)

/-- The local equation in a projective-line pencil datum can equivalently be
read using the free presentation of the actual pullback of the global Serre
bundle. -/
theorem SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData.localIdeal_eq_onGlobalBundle
    [IsSeparated f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (n : ℕ)
    (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n)
    (P : SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      f C seed n zeroDatum infinityDatum)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    P.datum.val.comap
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) =
      SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdealOnGlobalBundle
        f C seed ij := by
  rw [P.localIdeal_eq]
  exact SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal_eq_onGlobalBundle
    f C seed ij

/-- A global finite-subscheme pencil automatically restricts to the same
normalized zero ideal through either product chart on their common
parameter-chart overlap.  Thus the local equation field of
`ProjectiveLinePencilData` has the full descent compatibility required by
the projective-line cover. -/
theorem
    SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData.normalizedLocalPencilZeroIdeal_comap_overlap
    [IsSeparated f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) (n : ℕ)
    (zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n)
    (P : SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      f C seed n zeroDatum infinityDatum)
    (i : C.ι) (b c : Bool) :
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed (i, b)).comap
      (pullback.fst
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))) =
    (SerreExtensionRankTwoAffineCover.projectiveLineNormalizedLocalPencilZeroIdeal
      f C seed (i, c)).comap
      (pullback.snd
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, b))
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f (i, c))) := by
  rw [← P.localIdeal_eq (i, b), ← P.localIdeal_eq (i, c)]
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp]
  exact congrArg (fun q => P.datum.val.comap q) pullback.condition

/-- The global rank-two pencil data determines the finite-subscheme pencil
used by the existing rational-cycle-family machinery. -/
noncomputable def SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData.toFiniteSubschemeDatumPencil
    [IsSeparated f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) {n : ℕ}
    {zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n}
    (P : SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      f C seed n zeroDatum infinityDatum) :
    AllCharacteristics.FiniteSubschemeDatumPencil f n zeroDatum infinityDatum where
  datum := P.datum
  zeroIso := P.zeroIso
  zero_over := P.zero_over
  infinityIso := P.infinityIso
  infinity_over := P.infinity_over

/- The endpoint identifications of the projective-line Serre pencil feed
directly into the rational-cycle-family quotient: the two endpoint cycles
represent the same class. -/
theorem SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData.cycleClass_eq
    [IsSeparated f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) {n : ℕ}
    {zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n}
    (P : SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      f C seed n zeroDatum infinityDatum) :
    curveFamilyCycleClass f
        (AllCharacteristics.finiteSubschemeDatumCycle f zeroDatum).toZeroCycle =
      curveFamilyCycleClass f
        (AllCharacteristics.finiteSubschemeDatumCycle f infinityDatum).toZeroCycle := by
  exact AllCharacteristics.FiniteSubschemeDatumPencil.cycleClass_eq f
    (P.toFiniteSubschemeDatumPencil f C seed)

/-- Retarget the endpoint identifications of a normalized Serre pencil along
isomorphisms of the endpoint subschemes over the original surface.  The
global finite-flat family and its chartwise normalized equations are left
unchanged.  This is the form needed when the geometric construction first
identifies its literal endpoint zero loci with Voisin's residual subschemes. -/
noncomputable def SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData.retarget
    [IsSeparated f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) {n : ℕ}
    {zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n}
    (P : SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      f C seed n zeroDatum infinityDatum)
    (zeroDatum' infinityDatum' : AllCharacteristics.FiniteSubschemeDatum f n)
    (zeroIso : zeroDatum.val.subscheme ≅ zeroDatum'.val.subscheme)
    (zero_over : zeroIso.hom ≫ zeroDatum'.val.subschemeι = zeroDatum.val.subschemeι)
    (infinityIso : infinityDatum.val.subscheme ≅ infinityDatum'.val.subscheme)
    (infinity_over : infinityIso.hom ≫ infinityDatum'.val.subschemeι =
      infinityDatum.val.subschemeι) :
    SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      f C seed n zeroDatum' infinityDatum' where
  datum := P.datum
  localIdeal_eq := P.localIdeal_eq
  zeroIso := P.zeroIso ≪≫ zeroIso
  zero_over := by
    rw [Iso.trans_hom, Category.assoc, zero_over, P.zero_over]
  infinityIso := P.infinityIso ≪≫ infinityIso
  infinity_over := by
    rw [Iso.trans_hom, Category.assoc, infinity_over, P.infinity_over]

/-- Retargeting the two endpoint identifications preserves the quotient
cycle-class relation.  This is the form used when the normalized Serre
pencil is identified with Voisin's separately presented residual schemes. -/
theorem SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData.retarget_cycleClass_eq
    [IsSeparated f]
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e) {n : ℕ}
    {zeroDatum infinityDatum : AllCharacteristics.FiniteSubschemeDatum f n}
    (P : SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      f C seed n zeroDatum infinityDatum)
    (zeroDatum' infinityDatum' : AllCharacteristics.FiniteSubschemeDatum f n)
    (zeroIso : zeroDatum.val.subscheme ≅ zeroDatum'.val.subscheme)
    (zero_over : zeroIso.hom ≫ zeroDatum'.val.subschemeι = zeroDatum.val.subschemeι)
    (infinityIso : infinityDatum.val.subscheme ≅ infinityDatum'.val.subscheme)
    (infinity_over : infinityIso.hom ≫ infinityDatum'.val.subschemeι =
      infinityDatum.val.subschemeι) :
    curveFamilyCycleClass f
        (AllCharacteristics.finiteSubschemeDatumCycle f zeroDatum').toZeroCycle =
      curveFamilyCycleClass f
        (AllCharacteristics.finiteSubschemeDatumCycle f infinityDatum').toZeroCycle := by
  have hzero := AllCharacteristics.finiteSubschemeDatum_cycleClass_eq_of_iso
    f zeroDatum zeroDatum' zeroIso zero_over
  have hinfinity := AllCharacteristics.finiteSubschemeDatum_cycleClass_eq_of_iso
    f infinityDatum infinityDatum' infinityIso infinity_over
  calc
    curveFamilyCycleClass f
        (AllCharacteristics.finiteSubschemeDatumCycle f zeroDatum').toZeroCycle =
        curveFamilyCycleClass f
          (AllCharacteristics.finiteSubschemeDatumCycle f zeroDatum).toZeroCycle := hzero.symm
    _ = curveFamilyCycleClass f
          (AllCharacteristics.finiteSubschemeDatumCycle f infinityDatum).toZeroCycle :=
      P.cycleClass_eq f C seed
    _ = curveFamilyCycleClass f
          (AllCharacteristics.finiteSubschemeDatumCycle f infinityDatum').toZeroCycle := hinfinity

end

section

variable {K : Type u} [CommRing K] {X : Scheme.{u}}
  {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
  (f : X ⟶ Spec (.of K))

/-- The map from every affine product chart to the original surface is open.
It is the composition of the chart's open immersion into the parameter
space with the open projective-line projection. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toScheme_isOpenMap
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsOpenMap ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij ≫
      projectiveLineAmbientToScheme K f) := by
  exact (projectiveLineAmbientToScheme_isOpenMap K f).comp
    (show IsOpenMap ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) from
      (show IsOpenImmersion
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij) from inferInstance).base_open.isOpenMap)

/-- The pullback of the unit module to every affine pencil chart is
invertible.  This is the sheaf-theoretic prerequisite for pulling the two
Serre sections to that chart. -/
theorem SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_pullbackUnitComparison_isIso
    (C : SerreExtensionRankTwoAffineCover e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij ≫
        projectiveLineAmbientToScheme K f)) :=
  BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_toScheme_isOpenMap f C ij)

/-- The Serre-pencil section on one affine parameter chart.  The two
endomorphism coefficients are supplied by the corresponding normalized
projective-line chart; this definition performs the required pullback of the
canonical section and its chosen lift. -/
noncomputable def SerreExtensionRankTwoAffineCover.projectiveLineLocalPencilSection
    (C : SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionPencilSeed e)
    (ij : (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).I₀)
    (a b : SheafOfModules.unit
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf ⟶
      SheafOfModules.unit
        ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).X ij).ringCatSheaf) :
    ((AlgebraicGeometry.Scheme.Modules.pullback
      ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij ≫
        projectiveLineAmbientToScheme K f)).obj e.E).sections :=
  SerreExtensionPencilSeed.pullbackLinearCombinationSection e
    ((SerreExtensionRankTwoAffineCover.projectiveLineOpenCover f C).f ij ≫
      projectiveLineAmbientToScheme K f)
    (SerreExtensionRankTwoAffineCover.projectiveLineOpenCover_pullbackUnitComparison_isIso
      f C ij)
    seed a b

end

end SerreExtensionData

end PfaffianDescent
