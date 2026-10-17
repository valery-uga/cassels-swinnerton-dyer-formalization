import PfaffianDescent.QuadraticFullBaseLocusFiniteTriple
import PfaffianDescent.VoisinQuotientAmbientChart
import AllCharacteristics.AmbientChartPresentation
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! The FULL quadratic series of an actual projective subscheme, over every
field.  Each condition is a kernel of a map on scheme sections.  No radical,
carrier vanishing ideal, reducedness, or chosen global chart is involved. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

def intrinsicQuadraticAmbientOpen (j : Fin 4) :
    (Proj (homogeneousSubmodule (Fin 4) K)).affineOpens :=
  ⟨Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X j),
    Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K) (X j)
      (isHomogeneous_X K j) (by decide : 0 < 1)⟩

/-- Actual pullback vanishing on a standard affine open, expressed as a
polynomial ideal through normalized ambient evaluation. -/
def intrinsicQuadraticChartIdeal {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) (j : Fin 4) :
    Ideal (MvPolynomial (Fin 4) K) :=
  ((i.ker.ideal (intrinsicQuadraticAmbientOpen j)).comap
    (Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)).hom).comap
      (ambientChartEvaluation j)

/-- All homogeneous quadrics whose restrictions vanish on the actual
subscheme.  The four coordinate charts cover the ambient projective space. -/
def intrinsicFullQuadraticSystem {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  homogeneousSubmodule (Fin 4) K 2 ⊓
    ⨅ j : Fin 4, (intrinsicQuadraticChartIdeal i j).restrictScalars K

theorem intrinsicFullQuadraticSystem_homogeneous {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) K) (hp : p ∈ intrinsicFullQuadraticSystem i) :
    p.IsHomogeneous 2 := hp.1

def intrinsicFullQuadraticBaseIdeal {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) :=
  quadraticSystemBaseLocusIdeal (intrinsicFullQuadraticSystem i)
    (intrinsicFullQuadraticSystem_homogeneous i)

theorem intrinsicQuadraticAmbientOpen_iSup :
    ⨆ j : Fin 4, (intrinsicQuadraticAmbientOpen (K := K) j).1 = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ MvPolynomial.idealOfVars (Fin 4) K
  rw [← pow_one (MvPolynomial.idealOfVars (Fin 4) K),
    MvPolynomial.mem_pow_idealOfVars_iff]
  intro m hm
  have he : m.degree = n := by
    simpa only [Finsupp.degree_apply] using
      (IsHomogeneous.degree_eq_sum_deg_support hp hm).symm
  exact he ▸ hn

/-- The quotient chart preserves the actual coefficient homomorphism. -/
theorem quotientAmbientChartMap_baseMap
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4) (r : K) :
    quotientAmbientChartMap I j
      (AllCharacteristics.GradedChart.baseMap
        (homogeneousSubmodule (Fin 4) K) (z := X j) r) =
      chartBaseMap I j r := by
  let hx : X j ∈ homogeneousSubmodule (Fin 4) K 1 := isHomogeneous_X K j
  let hy : coordinate I j ∈ grading I 1 := coordinate_mem I j
  have hc : C r ∈ homogeneousSubmodule (Fin 4) K (0 • 1) := by
    simpa using isHomogeneous_C (σ := Fin 4) r
  have hm := AllCharacteristics.gradedAwayMapOfEq_mk (quotientGradedRingHom I)
    (X j) (coordinate I j) (quotientGradedRingHom_coordinate I j)
    hx hy 0 (C r) hc
  change AllCharacteristics.gradedAwayMapOfEq (quotientGradedRingHom I)
      (X j) (coordinate I j) (quotientGradedRingHom_coordinate I j)
      (Away.mk (homogeneousSubmodule (Fin 4) K) hx 0 (C r) hc) =
    Away.mk (grading I) hy 0 (Ideal.Quotient.mk I.toIdeal (C r))
      (by simpa using (polynomial_class_mem_grading I (C r)
        (isHomogeneous_C (σ := Fin 4) r)))
  exact hm

/-- The actual ambient quotient-chart kernel is the image of the entire
homogeneous ideal under ambient chart evaluation. -/
theorem quotientAmbientChartMap_ker_eq_ideal_image
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4) :
    RingHom.ker (quotientAmbientChartMap I j) =
      I.toIdeal.map (ambientChartEvaluation j) := by
  let f := quotientAmbientChartMap I j
  let evA := ambientChartEvaluation (R := K) (σ := Fin 4) j
  let evI := eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
  have hcomp : f.comp evA = evI := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, evA, evI, ambientChartEvaluation,
        eval₂Hom_C] using quotientAmbientChartMap_baseMap I j r
    · intro v
      simpa only [RingHom.comp_apply, evA, evI, ambientChartEvaluation,
        eval₂Hom_X', ambientChartCoordinate] using
        quotientAmbientChartMap_coordinate I j v
  have hker : RingHom.ker f = (chartPresentationIdeal I j).map evA := by
    apply le_antisymm
    · intro a ha
      obtain ⟨p, rfl⟩ := ambientChartEvaluation_surjective (R := K) (σ := Fin 4) j a
      apply Ideal.mem_map_of_mem evA
      rw [← chartEvaluation_ker I j]
      change evI p = 0
      rw [← hcomp]
      exact ha
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      change f (evA p) = 0
      rw [← RingHom.comp_apply, hcomp]
      change p ∈ RingHom.ker (eval₂Hom (chartBaseMap I j) (chartCoordinate I j))
      rw [chartEvaluation_ker I j]
      exact hp
  rw [hker]
  change (I.toIdeal ⊔ ambientChartPresentationIdeal j).map evA = _
  rw [Ideal.map_sup]
  have hA : (ambientChartPresentationIdeal (R := K) (σ := Fin 4) j).map evA = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker evA).mpr
    rw [ambientChartEvaluation_ker]
  rw [hA, sup_bot_eq]

set_option backward.isDefEq.respectTransparency false in
/-- Chartwise scheme-theoretic vanishing of the homogeneous ideal supplies
the actual projective kernel inclusion, with no geometric containment input. -/
theorem quotientProjMap_ker_le_of_intrinsic_chart_ideal
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (hI : ∀ j : Fin 4, I.toIdeal ≤ intrinsicQuadraticChartIdeal i j) :
    (quotientProjMap I).ker ≤ i.ker := by
  apply Scheme.IdealSheafData.le_of_iSup_eq_top
    intrinsicQuadraticAmbientOpen intrinsicQuadraticAmbientOpen_iSup
  intro j
  let U := intrinsicQuadraticAmbientOpen (K := K) j
  let evS := Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)
  letI : IsIso evS :=
    (Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) K) (X j)
      (isHomogeneous_X K j) (by decide)).isIso_hom
  have hsurj : Function.Surjective evS := (ConcreteCategory.bijective_of_isIso evS).2
  have hmap : I.toIdeal.map (ambientChartEvaluation j) ≤
      (i.ker.ideal U).comap evS.hom := by
    rw [Ideal.map_le_iff_le_comap]
    exact hI j
  intro s hs
  obtain ⟨a, rfl⟩ := hsurj s
  have hz : (quotientProjMap I).app U (evS a) = 0 := by
    rw [(quotientProjMap I).ker_apply U] at hs
    change (quotientProjMap I).app U (evS a) = 0 at hs
    exact hs
  have he := congrArg (fun g => g a)
    (Proj.awayToSection_comp_appLE (quotientGradedRingHom I)
      (irrelevant_le_map_quotientGradedRingHom I) (isHomogeneous_X K j))
  change (quotientProjMap I).app U (evS a) =
    Proj.awayToSection (grading I) (coordinate I j)
      (quotientAmbientChartMap I j a) at he
  have hzI : Proj.awayToSection (grading I) (coordinate I j)
      (quotientAmbientChartMap I j a) = 0 := he.symm.trans hz
  letI : IsIso (Proj.awayToSection (grading I) (coordinate I j)) :=
    (Proj.basicOpenIsoAway (grading I) (coordinate I j)
      (coordinate_mem I j) (by decide)).isIso_hom
  have ha : a ∈ RingHom.ker (quotientAmbientChartMap I j) := by
    change quotientAmbientChartMap I j a = 0
    apply (ConcreteCategory.bijective_of_isIso
      (Proj.awayToSection (grading I) (coordinate I j))).1
    simpa only [map_zero] using hzI
  rw [quotientAmbientChartMap_ker_eq_ideal_image] at ha
  exact hmap ha

/-- The entire intrinsic quadratic base scheme contains the original
subscheme scheme-theoretically. -/
theorem intrinsicFullQuadraticBaseIdeal_ker_le {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) :
    (quotientProjMap (intrinsicFullQuadraticBaseIdeal i)).ker ≤ i.ker := by
  apply quotientProjMap_ker_le_of_intrinsic_chart_ideal
  intro j
  apply Ideal.span_le.mpr
  intro p hp
  exact ((Submodule.mem_iInf _).mp hp.2) j

end PfaffianDescent
