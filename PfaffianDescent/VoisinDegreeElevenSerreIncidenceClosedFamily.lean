import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProjectivePlane
import PfaffianDescent.VoisinFixedLinearSystemUniversalZeroSubschemeGluing

/-! # Actual three-point incidence and its universal zero family

The incidence ideal is the sum of the three pullbacks of the actual universal
zero ideal.  Its closed subscheme therefore imposes vanishing at all three
marked points, without a supplied kernel or finite-zero certificate.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section Abstract
variable {S B X P Z : Scheme.{u}}
variable (b : B ⟶ S) (x : X ⟶ S) (p : P ⟶ S)
variable (marked : Fin 3 → (B ⟶ X)) (hmarked : ∀ i, marked i ≫ x = b)
variable (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]

def serreThreePointSectionIncidenceIdeal : (pullback b p).IdealSheafData :=
  ⨆ i : Fin 3, zero.ker.comap (fixedLinearSystemIncidenceMap b x p marked hmarked i)

abbrev serreThreePointSectionIncidence : Scheme.{u} :=
  (serreThreePointSectionIncidenceIdeal b x p marked hmarked zero).subscheme

abbrev serreThreePointSectionIncidenceToProduct :
    serreThreePointSectionIncidence b x p marked hmarked zero ⟶ pullback b p :=
  (serreThreePointSectionIncidenceIdeal b x p marked hmarked zero).subschemeι

abbrev serreThreePointSectionIncidenceToConfiguration :
    serreThreePointSectionIncidence b x p marked hmarked zero ⟶ B :=
  serreThreePointSectionIncidenceToProduct b x p marked hmarked zero ≫ pullback.fst b p

abbrev serreThreePointSectionIncidenceToParameters :
    serreThreePointSectionIncidence b x p marked hmarked zero ⟶ P :=
  serreThreePointSectionIncidenceToProduct b x p marked hmarked zero ≫ pullback.snd b p

/-- The incidence is a literal closed subscheme of configuration times parameters. -/
instance serreThreePointSectionIncidenceToProduct_isClosedImmersion :
    IsClosedImmersion (serreThreePointSectionIncidenceToProduct b x p marked hmarked zero) :=
  inferInstance

/-- Its points are exactly the simultaneous three marked zero conditions. -/
theorem serreThreePointSectionIncidence_range :
    Set.range (serreThreePointSectionIncidenceToProduct b x p marked hmarked zero) =
      {t | ∀ i : Fin 3,
        fixedLinearSystemIncidenceMap b x p marked hmarked i t ∈ Set.range zero} := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  change ((⨆ i : Fin 3, zero.ker.comap
    (fixedLinearSystemIncidenceMap b x p marked hmarked i)).support : Set (properFiniteIncidenceParameterSpace b p)) = _
  rw [Scheme.IdealSheafData.support_iSup]
  simp only [Scheme.IdealSheafData.support_comap]
  have hz : (zero.ker.support : Set (properFiniteIncidenceParameterSpace x p)) = Set.range zero := by
    rw [Scheme.Hom.support_ker, zero.isClosedEmbedding.isClosed_range.closure_eq]
  ext t
  simp only [TopologicalSpace.Closeds.coe_iInf, Set.mem_iInter,
    Set.mem_preimage, Set.mem_setOf_eq]
  apply forall_congr'
  intro i
  change fixedLinearSystemIncidenceMap b x p marked hmarked i t ∈
    (zero.ker.support : Set (properFiniteIncidenceParameterSpace x p)) ↔
      fixedLinearSystemIncidenceMap b x p marked hmarked i t ∈ Set.range zero
  rw [hz]

/-- Restrict the actual universal zero family to the actual incidence scheme. -/
abbrev serreThreePointSectionIncidenceZeroFamily :=
  pullback.snd (zero ≫ pullback.snd x p)
    (serreThreePointSectionIncidenceToParameters b x p marked hmarked zero)

/-- Properness of the universal zero family survives restriction to incidence. -/
instance serreThreePointSectionIncidenceZeroFamily_isProper
    [IsProper (zero ≫ pullback.snd x p)] :
    IsProper (serreThreePointSectionIncidenceZeroFamily b x p marked hmarked zero) :=
  inferInstance
end Abstract

/-- The globally glued zero scheme of an arbitrary finite-dimensional bundle
section system is proper over its actual projective section parameters when
the underlying scheme is proper.  This applies to the rank-two Serre bundle. -/
theorem serreSectionUniversalZeroToParameters_isProper
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsProper base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (C : SchemeModuleFiniteFreeAffineCover M ι) :
    IsProper (C.projectiveSectionLocalZeroGluedToAmbient base M ≫
      pullback.snd base (schemeModuleGlobalSectionsProjectiveParametersToBase base M)) := by
  letI := C.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  infer_instance

end PfaffianDescent
